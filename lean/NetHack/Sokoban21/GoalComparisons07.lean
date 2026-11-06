/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.GoalComparisons06
import NetHack.Sokoban21.Comparisons167
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem goalC910 (pattern : Twelve) (guard : d0 pattern = 1) : d816 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC911 (pattern : Twelve) (guard : d3251 pattern = 1) : d824 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC320 pattern childGuard
    simpa only [d3251, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC910 pattern childGuard
    simpa only [d3251, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC912 (pattern : Twelve) (guard : d3252 pattern = 1) : d838 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC324 pattern childGuard
    simpa only [d3252, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC911 pattern childGuard
    simpa only [d3252, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC913 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (0 : Int) + d4 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC914 (pattern : Twelve) (guard : d3247 pattern = 1) : d17 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC91 pattern childGuard
    simpa only [d3247, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d3285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC913 pattern childGuard
    simpa only [d3247, d3285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC915 (pattern : Twelve) (guard : d0 pattern = 1) : d17 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC916 (pattern : Twelve) (guard : d3251 pattern = 1) : d17 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC914 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC915 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC917 (pattern : Twelve) (guard : d3255 pattern = 1) : d839 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC916 pattern childGuard
    simpa only [d3255, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC785 pattern childGuard
    simpa only [d3255, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC918 (pattern : Twelve) (guard : d3256 pattern = 1) : d853 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC912 pattern childGuard
    simpa only [d3256, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC917 pattern childGuard
    simpa only [d3256, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC919 (pattern : Twelve) (guard : d3260 pattern = 1) : d1020 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1020, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC918 pattern childGuard
    simpa only [d3260, d1020, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1020, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC824 pattern childGuard
    simpa only [d3260, d1020, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC920 (pattern : Twelve) (guard : d0 pattern = 1) : d824 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC921 (pattern : Twelve) (guard : d3255 pattern = 1) : d838 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC340 pattern childGuard
    simpa only [d3255, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC920 pattern childGuard
    simpa only [d3255, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC922 (pattern : Twelve) (guard : d0 pattern = 1) : d839 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC923 (pattern : Twelve) (guard : d3259 pattern = 1) : d853 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC921 pattern childGuard
    simpa only [d3259, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC922 pattern childGuard
    simpa only [d3259, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC924 (pattern : Twelve) (guard : d3263 pattern = 1) : d1021 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1021, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC923 pattern childGuard
    simpa only [d3263, d1021, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1021, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3263, d1021, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC925 (pattern : Twelve) (guard : d3264 pattern = 1) : d1024 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d1024, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC919 pattern childGuard
    simpa only [d3264, d1024, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d1024, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC924 pattern childGuard
    simpa only [d3264, d1024, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC926 (pattern : Twelve) (guard : d3265 pattern = 1) : d1025 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3265, d1025, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC909 pattern childGuard
    simpa only [d3265, d1025, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3265, d1025, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC925 pattern childGuard
    simpa only [d3265, d1025, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC927 (pattern : Twelve) (guard : d3268 pattern = 1) : d1022 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1022 pattern).2
  change d1022 pattern ≤ (0 : Int) + 6
  omega
theorem goalC928 (pattern : Twelve) (guard : d3269 pattern = 1) : d1026 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3269, d1026, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC926 pattern childGuard
    simpa only [d3269, d1026, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3269, d1026, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC927 pattern childGuard
    simpa only [d3269, d1026, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC929 (pattern : Twelve) (guard : d3272 pattern = 1) : d1027 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1027 pattern).2
  change d1027 pattern ≤ (0 : Int) + 6
  omega
theorem goalC930 (pattern : Twelve) (guard : d3273 pattern = 1) : d1028 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3273, d1028, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC928 pattern childGuard
    simpa only [d3273, d1028, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3273, d1028, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC929 pattern childGuard
    simpa only [d3273, d1028, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC931 (pattern : Twelve) (guard : d3276 pattern = 1) : d1027 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1027 pattern).2
  change d1027 pattern ≤ (0 : Int) + 6
  omega
theorem goalC932 (pattern : Twelve) (guard : d3277 pattern = 1) : d1029 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3277, d1029, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC930 pattern childGuard
    simpa only [d3277, d1029, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3277, d1029, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC931 pattern childGuard
    simpa only [d3277, d1029, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC933 (pattern : Twelve) (guard : d3247 pattern = 1) : d818 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d818, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC739 pattern childGuard
    simpa only [d3247, d818, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d818, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d3247, d818, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC934 (pattern : Twelve) (guard : d3248 pattern = 1) : d1030 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC352 pattern childGuard
    simpa only [d3248, d1030, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC933 pattern childGuard
    simpa only [d3248, d1030, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC935 (pattern : Twelve) (guard : d3249 pattern = 1) : d1038 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC356 pattern childGuard
    simpa only [d3249, d1038, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC934 pattern childGuard
    simpa only [d3249, d1038, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC936 (pattern : Twelve) (guard : d3247 pattern = 1) : d36 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d36, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC745 pattern childGuard
    simpa only [d3247, d36, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d36, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5047 pattern childGuard
    simpa only [d3247, d36, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC937 (pattern : Twelve) (guard : d3248 pattern = 1) : d1031 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC352 pattern childGuard
    simpa only [d3248, d1031, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC936 pattern childGuard
    simpa only [d3248, d1031, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC938 (pattern : Twelve) (guard : d3251 pattern = 1) : d1032 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC20 pattern childGuard
    simpa only [d3251, d1032, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC751 pattern childGuard
    simpa only [d3251, d1032, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC939 (pattern : Twelve) (guard : d3252 pattern = 1) : d1039 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC937 pattern childGuard
    simpa only [d3252, d1039, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC938 pattern childGuard
    simpa only [d3252, d1039, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC940 (pattern : Twelve) (guard : d3253 pattern = 1) : d1048 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC935 pattern childGuard
    simpa only [d3253, d1048, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC939 pattern childGuard
    simpa only [d3253, d1048, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC941 (pattern : Twelve) (guard : d3251 pattern = 1) : d1033 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC363 pattern childGuard
    simpa only [d3251, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC756 pattern childGuard
    simpa only [d3251, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC942 (pattern : Twelve) (guard : d3252 pattern = 1) : d1040 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC367 pattern childGuard
    simpa only [d3252, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC941 pattern childGuard
    simpa only [d3252, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC943 (pattern : Twelve) (guard : d3251 pattern = 1) : d36 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC363 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC759 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC944 (pattern : Twelve) (guard : d0 pattern = 1) : d1032 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC945 (pattern : Twelve) (guard : d3255 pattern = 1) : d1041 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC943 pattern childGuard
    simpa only [d3255, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC944 pattern childGuard
    simpa only [d3255, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC946 (pattern : Twelve) (guard : d3256 pattern = 1) : d1049 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC942 pattern childGuard
    simpa only [d3256, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC945 pattern childGuard
    simpa only [d3256, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC947 (pattern : Twelve) (guard : d3257 pattern = 1) : d1054 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d1054, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC940 pattern childGuard
    simpa only [d3257, d1054, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d1054, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC946 pattern childGuard
    simpa only [d3257, d1054, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC948 (pattern : Twelve) (guard : d0 pattern = 1) : d1033 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC949 (pattern : Twelve) (guard : d3255 pattern = 1) : d1042 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC376 pattern childGuard
    simpa only [d3255, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC948 pattern childGuard
    simpa only [d3255, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC950 (pattern : Twelve) (guard : d0 pattern = 1) : d1041 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC951 (pattern : Twelve) (guard : d3259 pattern = 1) : d1050 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC949 pattern childGuard
    simpa only [d3259, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC950 pattern childGuard
    simpa only [d3259, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC952 (pattern : Twelve) (guard : d3260 pattern = 1) : d1055 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1055, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC946 pattern childGuard
    simpa only [d3260, d1055, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1055, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC951 pattern childGuard
    simpa only [d3260, d1055, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC953 (pattern : Twelve) (guard : d3261 pattern = 1) : d1060 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d1060, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC947 pattern childGuard
    simpa only [d3261, d1060, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d1060, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC952 pattern childGuard
    simpa only [d3261, d1060, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC954 (pattern : Twelve) (guard : d0 pattern = 1) : d818 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC955 (pattern : Twelve) (guard : d3251 pattern = 1) : d1033 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC385 pattern childGuard
    simpa only [d3251, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC954 pattern childGuard
    simpa only [d3251, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC956 (pattern : Twelve) (guard : d3252 pattern = 1) : d1043 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC389 pattern childGuard
    simpa only [d3252, d1043, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC955 pattern childGuard
    simpa only [d3252, d1043, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC957 (pattern : Twelve) (guard : d0 pattern = 1) : d36 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC958 (pattern : Twelve) (guard : d3251 pattern = 1) : d36 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC385 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC957 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC959 (pattern : Twelve) (guard : d0 pattern = 1) : d1032 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC960 (pattern : Twelve) (guard : d3255 pattern = 1) : d1041 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC958 pattern childGuard
    simpa only [d3255, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC959 pattern childGuard
    simpa only [d3255, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC961 (pattern : Twelve) (guard : d3256 pattern = 1) : d1051 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC956 pattern childGuard
    simpa only [d3256, d1051, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC960 pattern childGuard
    simpa only [d3256, d1051, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC962 (pattern : Twelve) (guard : d0 pattern = 1) : d1034 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC963 (pattern : Twelve) (guard : d3255 pattern = 1) : d1044 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC397 pattern childGuard
    simpa only [d3255, d1044, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC962 pattern childGuard
    simpa only [d3255, d1044, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC964 (pattern : Twelve) (guard : d0 pattern = 1) : d1045 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC965 (pattern : Twelve) (guard : d3259 pattern = 1) : d1052 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC963 pattern childGuard
    simpa only [d3259, d1052, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC964 pattern childGuard
    simpa only [d3259, d1052, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC966 (pattern : Twelve) (guard : d3260 pattern = 1) : d1056 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1056, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC961 pattern childGuard
    simpa only [d3260, d1056, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1056, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC965 pattern childGuard
    simpa only [d3260, d1056, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC967 (pattern : Twelve) (guard : d0 pattern = 1) : d1033 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC968 (pattern : Twelve) (guard : d3255 pattern = 1) : d1042 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC406 pattern childGuard
    simpa only [d3255, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC967 pattern childGuard
    simpa only [d3255, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC969 (pattern : Twelve) (guard : d0 pattern = 1) : d1041 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC970 (pattern : Twelve) (guard : d3259 pattern = 1) : d1050 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC968 pattern childGuard
    simpa only [d3259, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC969 pattern childGuard
    simpa only [d3259, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC971 (pattern : Twelve) (guard : d3263 pattern = 1) : d1057 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1057, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC970 pattern childGuard
    simpa only [d3263, d1057, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1057, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3263, d1057, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC972 (pattern : Twelve) (guard : d3264 pattern = 1) : d1061 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d1061, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC966 pattern childGuard
    simpa only [d3264, d1061, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d1061, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC971 pattern childGuard
    simpa only [d3264, d1061, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC973 (pattern : Twelve) (guard : d3265 pattern = 1) : d1064 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3265, d1064, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC953 pattern childGuard
    simpa only [d3265, d1064, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3265, d1064, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC972 pattern childGuard
    simpa only [d3265, d1064, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC974 (pattern : Twelve) (guard : d3268 pattern = 1) : d1065 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1065 pattern).2
  change d1065 pattern ≤ (0 : Int) + 6
  omega
theorem goalC975 (pattern : Twelve) (guard : d3269 pattern = 1) : d1067 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3269, d1067, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC973 pattern childGuard
    simpa only [d3269, d1067, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3269, d1067, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC974 pattern childGuard
    simpa only [d3269, d1067, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC976 (pattern : Twelve) (guard : d3272 pattern = 1) : d1065 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1065 pattern).2
  change d1065 pattern ≤ (0 : Int) + 6
  omega
theorem goalC977 (pattern : Twelve) (guard : d3273 pattern = 1) : d1068 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3273, d1068, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC975 pattern childGuard
    simpa only [d3273, d1068, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3273, d1068, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC976 pattern childGuard
    simpa only [d3273, d1068, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC978 (pattern : Twelve) (guard : d3276 pattern = 1) : d1066 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1066 pattern).2
  change d1066 pattern ≤ (0 : Int) + 6
  omega
theorem goalC979 (pattern : Twelve) (guard : d3277 pattern = 1) : d1069 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3277, d1069, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC977 pattern childGuard
    simpa only [d3277, d1069, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3277, d1069, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC978 pattern childGuard
    simpa only [d3277, d1069, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC980 (pattern : Twelve) (guard : d3252 pattern = 1) : d1070 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC748 pattern childGuard
    simpa only [d3252, d1070, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC813 pattern childGuard
    simpa only [d3252, d1070, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC981 (pattern : Twelve) (guard : d3253 pattern = 1) : d1078 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC420 pattern childGuard
    simpa only [d3253, d1078, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC980 pattern childGuard
    simpa only [d3253, d1078, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC982 (pattern : Twelve) (guard : d3252 pattern = 1) : d1071 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC755 pattern childGuard
    simpa only [d3252, d1071, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC174 pattern childGuard
    simpa only [d3252, d1071, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC983 (pattern : Twelve) (guard : d3255 pattern = 1) : d1072 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC760 pattern childGuard
    simpa only [d3255, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC173 pattern childGuard
    simpa only [d3255, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC984 (pattern : Twelve) (guard : d3256 pattern = 1) : d1079 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC982 pattern childGuard
    simpa only [d3256, d1079, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC983 pattern childGuard
    simpa only [d3256, d1079, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC985 (pattern : Twelve) (guard : d3257 pattern = 1) : d1088 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d1088, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC981 pattern childGuard
    simpa only [d3257, d1088, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d1088, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC984 pattern childGuard
    simpa only [d3257, d1088, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC986 (pattern : Twelve) (guard : d3255 pattern = 1) : d1073 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC771 pattern childGuard
    simpa only [d3255, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC173 pattern childGuard
    simpa only [d3255, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC987 (pattern : Twelve) (guard : d3256 pattern = 1) : d1080 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC427 pattern childGuard
    simpa only [d3256, d1080, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC986 pattern childGuard
    simpa only [d3256, d1080, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC988 (pattern : Twelve) (guard : d0 pattern = 1) : d1072 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC989 (pattern : Twelve) (guard : d3259 pattern = 1) : d1081 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC430 pattern childGuard
    simpa only [d3259, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC988 pattern childGuard
    simpa only [d3259, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC990 (pattern : Twelve) (guard : d3260 pattern = 1) : d1089 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1089, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC987 pattern childGuard
    simpa only [d3260, d1089, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1089, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC989 pattern childGuard
    simpa only [d3260, d1089, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC991 (pattern : Twelve) (guard : d3261 pattern = 1) : d1095 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d1095, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC985 pattern childGuard
    simpa only [d3261, d1095, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d1095, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC990 pattern childGuard
    simpa only [d3261, d1095, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC992 (pattern : Twelve) (guard : d3255 pattern = 1) : d1074 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC784 pattern childGuard
    simpa only [d3255, d1074, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC197 pattern childGuard
    simpa only [d3255, d1074, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC993 (pattern : Twelve) (guard : d3256 pattern = 1) : d1082 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC435 pattern childGuard
    simpa only [d3256, d1082, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC992 pattern childGuard
    simpa only [d3256, d1082, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC994 (pattern : Twelve) (guard : d0 pattern = 1) : d1075 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC995 (pattern : Twelve) (guard : d3259 pattern = 1) : d1083 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC438 pattern childGuard
    simpa only [d3259, d1083, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC994 pattern childGuard
    simpa only [d3259, d1083, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC996 (pattern : Twelve) (guard : d3260 pattern = 1) : d1090 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1090, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC993 pattern childGuard
    simpa only [d3260, d1090, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1090, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC995 pattern childGuard
    simpa only [d3260, d1090, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC997 (pattern : Twelve) (guard : d0 pattern = 1) : d1072 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC998 (pattern : Twelve) (guard : d3259 pattern = 1) : d1081 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC442 pattern childGuard
    simpa only [d3259, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC997 pattern childGuard
    simpa only [d3259, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC999 (pattern : Twelve) (guard : d3263 pattern = 1) : d1091 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d1091, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC998 pattern childGuard
    simpa only [d3263, d1091, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d1091, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3263, d1091, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1000 (pattern : Twelve) (guard : d3264 pattern = 1) : d1096 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d1096, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC996 pattern childGuard
    simpa only [d3264, d1096, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d1096, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC999 pattern childGuard
    simpa only [d3264, d1096, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1001 (pattern : Twelve) (guard : d3265 pattern = 1) : d1099 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3265, d1099, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC991 pattern childGuard
    simpa only [d3265, d1099, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3265, d1099, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1000 pattern childGuard
    simpa only [d3265, d1099, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1002 (pattern : Twelve) (guard : d3268 pattern = 1) : d1100 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1100 pattern).2
  change d1100 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1003 (pattern : Twelve) (guard : d3269 pattern = 1) : d1102 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3269, d1102, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1001 pattern childGuard
    simpa only [d3269, d1102, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3269, d1102, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1002 pattern childGuard
    simpa only [d3269, d1102, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1004 (pattern : Twelve) (guard : d3272 pattern = 1) : d1100 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1100 pattern).2
  change d1100 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1005 (pattern : Twelve) (guard : d3273 pattern = 1) : d1103 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3273, d1103, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1003 pattern childGuard
    simpa only [d3273, d1103, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3273, d1103, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1004 pattern childGuard
    simpa only [d3273, d1103, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1006 (pattern : Twelve) (guard : d3276 pattern = 1) : d1101 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1101 pattern).2
  change d1101 pattern ≤ (0 : Int) + 6
  omega
theorem goalC1007 (pattern : Twelve) (guard : d3277 pattern = 1) : d1104 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3277, d1104, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1005 pattern childGuard
    simpa only [d3277, d1104, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3277, d1104, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1006 pattern childGuard
    simpa only [d3277, d1104, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1008 (pattern : Twelve) (guard : d1867 pattern = 1) : d1105 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c7730 pattern childGuard
    simpa only [d1867, d1105, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c881 pattern childGuard
    simpa only [d1867, d1105, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1009 (pattern : Twelve) (guard : d0 pattern = 1) : d479 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1010 (pattern : Twelve) (guard : d3247 pattern = 1) : d1108 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d1108, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1008 pattern childGuard
    simpa only [d3247, d1108, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d1108, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1009 pattern childGuard
    simpa only [d3247, d1108, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1011 (pattern : Twelve) (guard : d3248 pattern = 1) : d1118 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC459 pattern childGuard
    simpa only [d3248, d1118, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1010 pattern childGuard
    simpa only [d3248, d1118, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1012 (pattern : Twelve) (guard : d3249 pattern = 1) : d1132 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC465 pattern childGuard
    simpa only [d3249, d1132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1011 pattern childGuard
    simpa only [d3249, d1132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1013 (pattern : Twelve) (guard : d1867 pattern = 1) : d480 pattern ≤ (0 : Int) + d0 pattern := by
  cases selected : pattern.k with
  | false =>
    have childGuard : d1866 pattern = 1 := by simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c3256 pattern childGuard
    simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c881 pattern childGuard
    simpa only [d1867, d480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1014 (pattern : Twelve) (guard : d0 pattern = 1) : d480 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1015 (pattern : Twelve) (guard : d3247 pattern = 1) : d480 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1013 pattern childGuard
    simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1014 pattern childGuard
    simpa only [d3247, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1016 (pattern : Twelve) (guard : d3248 pattern = 1) : d1119 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC464 pattern childGuard
    simpa only [d3248, d1119, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d1119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1015 pattern childGuard
    simpa only [d3248, d1119, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1017 (pattern : Twelve) (guard : d0 pattern = 1) : d495 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1018 (pattern : Twelve) (guard : d3247 pattern = 1) : d1109 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d1109, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC468 pattern childGuard
    simpa only [d3247, d1109, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d1109, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1017 pattern childGuard
    simpa only [d3247, d1109, d26, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1019 (pattern : Twelve) (guard : d0 pattern = 1) : d522 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1020 (pattern : Twelve) (guard : d3251 pattern = 1) : d1120 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1018 pattern childGuard
    simpa only [d3251, d1120, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1019 pattern childGuard
    simpa only [d3251, d1120, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1021 (pattern : Twelve) (guard : d3252 pattern = 1) : d1133 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1016 pattern childGuard
    simpa only [d3252, d1133, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1020 pattern childGuard
    simpa only [d3252, d1133, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1022 (pattern : Twelve) (guard : d3253 pattern = 1) : d1152 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1012 pattern childGuard
    simpa only [d3253, d1152, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1021 pattern childGuard
    simpa only [d3253, d1152, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1023 (pattern : Twelve) (guard : d3247 pattern = 1) : d515 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1867 pattern = 1 := by simpa only [d3247, d515, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC483 pattern childGuard
    simpa only [d3247, d515, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3247, d515, d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d3247, d515, d778, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1024 (pattern : Twelve) (guard : d3248 pattern = 1) : d1121 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC482 pattern childGuard
    simpa only [d3248, d1121, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d1121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1023 pattern childGuard
    simpa only [d3248, d1121, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1025 (pattern : Twelve) (guard : d0 pattern = 1) : d1110 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1026 (pattern : Twelve) (guard : d3251 pattern = 1) : d1122 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC491 pattern childGuard
    simpa only [d3251, d1122, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d1122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1025 pattern childGuard
    simpa only [d3251, d1122, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1027 (pattern : Twelve) (guard : d3252 pattern = 1) : d1134 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1024 pattern childGuard
    simpa only [d3252, d1134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1026 pattern childGuard
    simpa only [d3252, d1134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1028 (pattern : Twelve) (guard : d0 pattern = 1) : d515 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1029 (pattern : Twelve) (guard : d3251 pattern = 1) : d544 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC491 pattern childGuard
    simpa only [d3251, d544, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1028 pattern childGuard
    simpa only [d3251, d544, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1030 (pattern : Twelve) (guard : d0 pattern = 1) : d1120 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1031 (pattern : Twelve) (guard : d3255 pattern = 1) : d1135 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1029 pattern childGuard
    simpa only [d3255, d1135, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1030 pattern childGuard
    simpa only [d3255, d1135, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1032 (pattern : Twelve) (guard : d3256 pattern = 1) : d1153 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1027 pattern childGuard
    simpa only [d3256, d1153, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d1153, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1031 pattern childGuard
    simpa only [d3256, d1153, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1033 (pattern : Twelve) (guard : d3257 pattern = 1) : d1164 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d1164, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1022 pattern childGuard
    simpa only [d3257, d1164, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d1164, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1032 pattern childGuard
    simpa only [d3257, d1164, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1034 (pattern : Twelve) (guard : d0 pattern = 1) : d1108 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1035 (pattern : Twelve) (guard : d3251 pattern = 1) : d1123 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC506 pattern childGuard
    simpa only [d3251, d1123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d1123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1034 pattern childGuard
    simpa only [d3251, d1123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1036 (pattern : Twelve) (guard : d3252 pattern = 1) : d1136 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC511 pattern childGuard
    simpa only [d3252, d1136, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d1136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1035 pattern childGuard
    simpa only [d3252, d1136, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1037 (pattern : Twelve) (guard : d0 pattern = 1) : d480 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC1038 (pattern : Twelve) (guard : d3251 pattern = 1) : d480 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC510 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1037 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC1039 (pattern : Twelve) (guard : d3255 pattern = 1) : d1137 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1038 pattern childGuard
    simpa only [d3255, d1137, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d1137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC1030 pattern childGuard
    simpa only [d3255, d1137, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
