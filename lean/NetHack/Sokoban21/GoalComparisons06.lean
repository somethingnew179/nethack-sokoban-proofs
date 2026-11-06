/- Stage-only soko2-1 exact finite geometry/numeric wrapper. -/
import NetHack.Sokoban21.GoalComparisons05
import NetHack.Sokoban21.Comparisons167
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem goalC780 (pattern : Twelve) (guard : d0 pattern = 1) : d819 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC781 (pattern : Twelve) (guard : d3251 pattern = 1) : d828 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC99 pattern childGuard
    simpa only [d3251, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC780 pattern childGuard
    simpa only [d3251, d828, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC782 (pattern : Twelve) (guard : d3252 pattern = 1) : d842 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC97 pattern childGuard
    simpa only [d3252, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC781 pattern childGuard
    simpa only [d3252, d842, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC783 (pattern : Twelve) (guard : d0 pattern = 1) : d34 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC784 (pattern : Twelve) (guard : d3251 pattern = 1) : d34 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC99 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC783 pattern childGuard
    simpa only [d3251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC785 (pattern : Twelve) (guard : d0 pattern = 1) : d825 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC786 (pattern : Twelve) (guard : d3255 pattern = 1) : d843 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC784 pattern childGuard
    simpa only [d3255, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC785 pattern childGuard
    simpa only [d3255, d843, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC787 (pattern : Twelve) (guard : d3256 pattern = 1) : d855 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC782 pattern childGuard
    simpa only [d3256, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC786 pattern childGuard
    simpa only [d3256, d855, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC788 (pattern : Twelve) (guard : d0 pattern = 1) : d829 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC789 (pattern : Twelve) (guard : d3255 pattern = 1) : d844 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC114 pattern childGuard
    simpa only [d3255, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC788 pattern childGuard
    simpa only [d3255, d844, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC790 (pattern : Twelve) (guard : d0 pattern = 1) : d845 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC791 (pattern : Twelve) (guard : d3259 pattern = 1) : d856 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC789 pattern childGuard
    simpa only [d3259, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC790 pattern childGuard
    simpa only [d3259, d856, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC792 (pattern : Twelve) (guard : d3260 pattern = 1) : d862 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d862, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC787 pattern childGuard
    simpa only [d3260, d862, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d862, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC791 pattern childGuard
    simpa only [d3260, d862, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC793 (pattern : Twelve) (guard : d0 pattern = 1) : d826 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC794 (pattern : Twelve) (guard : d3255 pattern = 1) : d840 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC130 pattern childGuard
    simpa only [d3255, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC793 pattern childGuard
    simpa only [d3255, d840, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC795 (pattern : Twelve) (guard : d0 pattern = 1) : d841 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC796 (pattern : Twelve) (guard : d3259 pattern = 1) : d854 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC794 pattern childGuard
    simpa only [d3259, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC795 pattern childGuard
    simpa only [d3259, d854, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC797 (pattern : Twelve) (guard : d3263 pattern = 1) : d863 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d863, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC796 pattern childGuard
    simpa only [d3263, d863, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d863, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3263, d863, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC798 (pattern : Twelve) (guard : d3264 pattern = 1) : d867 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d867, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC792 pattern childGuard
    simpa only [d3264, d867, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d867, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC797 pattern childGuard
    simpa only [d3264, d867, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC799 (pattern : Twelve) (guard : d3265 pattern = 1) : d869 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3265, d869, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC779 pattern childGuard
    simpa only [d3265, d869, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3265, d869, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC798 pattern childGuard
    simpa only [d3265, d869, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC800 (pattern : Twelve) (guard : d3268 pattern = 1) : d870 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range870 pattern).2
  change d870 pattern ≤ (0 : Int) + 6
  omega
theorem goalC801 (pattern : Twelve) (guard : d3269 pattern = 1) : d871 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3269, d871, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC799 pattern childGuard
    simpa only [d3269, d871, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3269, d871, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC800 pattern childGuard
    simpa only [d3269, d871, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC802 (pattern : Twelve) (guard : d3272 pattern = 1) : d871 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range871 pattern).2
  change d871 pattern ≤ (0 : Int) + 6
  omega
theorem goalC803 (pattern : Twelve) (guard : d3273 pattern = 1) : d871 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3273, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC801 pattern childGuard
    simpa only [d3273, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3273, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC802 pattern childGuard
    simpa only [d3273, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC804 (pattern : Twelve) (guard : d3276 pattern = 1) : d871 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range871 pattern).2
  change d871 pattern ≤ (0 : Int) + 6
  omega
theorem goalC805 (pattern : Twelve) (guard : d3277 pattern = 1) : d871 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3277, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC803 pattern childGuard
    simpa only [d3277, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3277, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC804 pattern childGuard
    simpa only [d3277, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC806 (pattern : Twelve) (guard : d3268 pattern = 1) : d869 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range869 pattern).2
  change d869 pattern ≤ (0 : Int) + 6
  omega
theorem goalC807 (pattern : Twelve) (guard : d3269 pattern = 1) : d869 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3269, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC799 pattern childGuard
    simpa only [d3269, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3269, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC806 pattern childGuard
    simpa only [d3269, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC808 (pattern : Twelve) (guard : d3272 pattern = 1) : d869 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range869 pattern).2
  change d869 pattern ≤ (0 : Int) + 6
  omega
theorem goalC809 (pattern : Twelve) (guard : d3273 pattern = 1) : d869 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3273, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC807 pattern childGuard
    simpa only [d3273, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3273, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC808 pattern childGuard
    simpa only [d3273, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC810 (pattern : Twelve) (guard : d3276 pattern = 1) : d906 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range906 pattern).2
  change d906 pattern ≤ (0 : Int) + 6
  omega
theorem goalC811 (pattern : Twelve) (guard : d3277 pattern = 1) : d907 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3277, d907, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC809 pattern childGuard
    simpa only [d3277, d907, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3277, d907, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC810 pattern childGuard
    simpa only [d3277, d907, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC812 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d26 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC813 (pattern : Twelve) (guard : d3251 pattern = 1) : d908 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC159 pattern childGuard
    simpa only [d3251, d908, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC812 pattern childGuard
    simpa only [d3251, d908, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC814 (pattern : Twelve) (guard : d3252 pattern = 1) : d909 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC160 pattern childGuard
    simpa only [d3252, d909, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC813 pattern childGuard
    simpa only [d3252, d909, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC815 (pattern : Twelve) (guard : d3253 pattern = 1) : d912 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC161 pattern childGuard
    simpa only [d3253, d912, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC814 pattern childGuard
    simpa only [d3253, d912, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC816 (pattern : Twelve) (guard : d3255 pattern = 1) : d910 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC174 pattern childGuard
    simpa only [d3255, d910, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC173 pattern childGuard
    simpa only [d3255, d910, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC817 (pattern : Twelve) (guard : d3256 pattern = 1) : d913 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC175 pattern childGuard
    simpa only [d3256, d913, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC816 pattern childGuard
    simpa only [d3256, d913, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC818 (pattern : Twelve) (guard : d3257 pattern = 1) : d917 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d917, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC815 pattern childGuard
    simpa only [d3257, d917, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d917, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC817 pattern childGuard
    simpa only [d3257, d917, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC819 (pattern : Twelve) (guard : d3259 pattern = 1) : d914 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC187 pattern childGuard
    simpa only [d3259, d914, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC184 pattern childGuard
    simpa only [d3259, d914, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC820 (pattern : Twelve) (guard : d3260 pattern = 1) : d918 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d918, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC817 pattern childGuard
    simpa only [d3260, d918, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d918, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC819 pattern childGuard
    simpa only [d3260, d918, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC821 (pattern : Twelve) (guard : d3261 pattern = 1) : d921 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d921, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC818 pattern childGuard
    simpa only [d3261, d921, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d921, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC820 pattern childGuard
    simpa only [d3261, d921, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC822 (pattern : Twelve) (guard : d3255 pattern = 1) : d911 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC198 pattern childGuard
    simpa only [d3255, d911, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC197 pattern childGuard
    simpa only [d3255, d911, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC823 (pattern : Twelve) (guard : d3256 pattern = 1) : d915 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC199 pattern childGuard
    simpa only [d3256, d915, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC822 pattern childGuard
    simpa only [d3256, d915, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC824 (pattern : Twelve) (guard : d3259 pattern = 1) : d916 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC208 pattern childGuard
    simpa only [d3259, d916, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC205 pattern childGuard
    simpa only [d3259, d916, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC825 (pattern : Twelve) (guard : d3260 pattern = 1) : d919 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d919, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC823 pattern childGuard
    simpa only [d3260, d919, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d919, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC824 pattern childGuard
    simpa only [d3260, d919, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC826 (pattern : Twelve) (guard : d3263 pattern = 1) : d920 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d920, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC824 pattern childGuard
    simpa only [d3263, d920, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d920, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3263, d920, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC827 (pattern : Twelve) (guard : d3264 pattern = 1) : d922 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d922, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC825 pattern childGuard
    simpa only [d3264, d922, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d922, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC826 pattern childGuard
    simpa only [d3264, d922, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC828 (pattern : Twelve) (guard : d3265 pattern = 1) : d923 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3265, d923, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC821 pattern childGuard
    simpa only [d3265, d923, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3265, d923, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC827 pattern childGuard
    simpa only [d3265, d923, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC829 (pattern : Twelve) (guard : d3268 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem goalC830 (pattern : Twelve) (guard : d3269 pattern = 1) : d924 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3269, d924, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC828 pattern childGuard
    simpa only [d3269, d924, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3269, d924, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC829 pattern childGuard
    simpa only [d3269, d924, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC831 (pattern : Twelve) (guard : d3272 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem goalC832 (pattern : Twelve) (guard : d3273 pattern = 1) : d925 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3273, d925, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC830 pattern childGuard
    simpa only [d3273, d925, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3273, d925, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC831 pattern childGuard
    simpa only [d3273, d925, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC833 (pattern : Twelve) (guard : d3276 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem goalC834 (pattern : Twelve) (guard : d3277 pattern = 1) : d926 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3277, d926, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC832 pattern childGuard
    simpa only [d3277, d926, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3277, d926, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC833 pattern childGuard
    simpa only [d3277, d926, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC835 (pattern : Twelve) (guard : d3261 pattern = 1) : d927 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d927, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC764 pattern childGuard
    simpa only [d3261, d927, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d927, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC820 pattern childGuard
    simpa only [d3261, d927, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC836 (pattern : Twelve) (guard : d3264 pattern = 1) : d928 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d928, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC792 pattern childGuard
    simpa only [d3264, d928, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d928, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC826 pattern childGuard
    simpa only [d3264, d928, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC837 (pattern : Twelve) (guard : d3265 pattern = 1) : d933 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3265, d933, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC835 pattern childGuard
    simpa only [d3265, d933, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3265, d933, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC836 pattern childGuard
    simpa only [d3265, d933, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC838 (pattern : Twelve) (guard : d3268 pattern = 1) : d934 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range934 pattern).2
  change d934 pattern ≤ (0 : Int) + 6
  omega
theorem goalC839 (pattern : Twelve) (guard : d3269 pattern = 1) : d936 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3269, d936, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC837 pattern childGuard
    simpa only [d3269, d936, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3269, d936, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC838 pattern childGuard
    simpa only [d3269, d936, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC840 (pattern : Twelve) (guard : d3272 pattern = 1) : d937 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range937 pattern).2
  change d937 pattern ≤ (0 : Int) + 6
  omega
theorem goalC841 (pattern : Twelve) (guard : d3273 pattern = 1) : d938 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3273, d938, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC839 pattern childGuard
    simpa only [d3273, d938, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3273, d938, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC840 pattern childGuard
    simpa only [d3273, d938, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC842 (pattern : Twelve) (guard : d3276 pattern = 1) : d937 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range937 pattern).2
  change d937 pattern ≤ (0 : Int) + 6
  omega
theorem goalC843 (pattern : Twelve) (guard : d3277 pattern = 1) : d939 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3277, d939, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC841 pattern childGuard
    simpa only [d3277, d939, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3277, d939, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC842 pattern childGuard
    simpa only [d3277, d939, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC844 (pattern : Twelve) (guard : d3248 pattern = 1) : d940 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC7 pattern childGuard
    simpa only [d3248, d940, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC159 pattern childGuard
    simpa only [d3248, d940, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC845 (pattern : Twelve) (guard : d3249 pattern = 1) : d947 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3245 pattern = 1 := by simpa only [d3249, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC232 pattern childGuard
    simpa only [d3249, d947, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3249, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC844 pattern childGuard
    simpa only [d3249, d947, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC846 (pattern : Twelve) (guard : d3248 pattern = 1) : d941 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3244 pattern = 1 := by simpa only [d3248, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC744 pattern childGuard
    simpa only [d3248, d941, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3248, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC159 pattern childGuard
    simpa only [d3248, d941, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC847 (pattern : Twelve) (guard : d3251 pattern = 1) : d942 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC750 pattern childGuard
    simpa only [d3251, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC812 pattern childGuard
    simpa only [d3251, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC848 (pattern : Twelve) (guard : d3252 pattern = 1) : d948 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC846 pattern childGuard
    simpa only [d3252, d948, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC847 pattern childGuard
    simpa only [d3252, d948, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC849 (pattern : Twelve) (guard : d3253 pattern = 1) : d955 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC845 pattern childGuard
    simpa only [d3253, d955, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC848 pattern childGuard
    simpa only [d3253, d955, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC850 (pattern : Twelve) (guard : d0 pattern = 1) : d942 pattern ≤ (0 : Int) + d778 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC851 (pattern : Twelve) (guard : d3255 pattern = 1) : d949 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC239 pattern childGuard
    simpa only [d3255, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC850 pattern childGuard
    simpa only [d3255, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC852 (pattern : Twelve) (guard : d3256 pattern = 1) : d956 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC240 pattern childGuard
    simpa only [d3256, d956, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC851 pattern childGuard
    simpa only [d3256, d956, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC853 (pattern : Twelve) (guard : d3257 pattern = 1) : d963 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d963, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC849 pattern childGuard
    simpa only [d3257, d963, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d963, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC852 pattern childGuard
    simpa only [d3257, d963, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC854 (pattern : Twelve) (guard : d3251 pattern = 1) : d943 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC60 pattern childGuard
    simpa only [d3251, d943, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC173 pattern childGuard
    simpa only [d3251, d943, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC855 (pattern : Twelve) (guard : d3252 pattern = 1) : d950 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3248 pattern = 1 := by simpa only [d3252, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC246 pattern childGuard
    simpa only [d3252, d950, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3252, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC854 pattern childGuard
    simpa only [d3252, d950, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC856 (pattern : Twelve) (guard : d3251 pattern = 1) : d944 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d3247 pattern = 1 := by simpa only [d3251, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC769 pattern childGuard
    simpa only [d3251, d944, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3251, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC173 pattern childGuard
    simpa only [d3251, d944, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC857 (pattern : Twelve) (guard : d3255 pattern = 1) : d951 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC856 pattern childGuard
    simpa only [d3255, d951, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC850 pattern childGuard
    simpa only [d3255, d951, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC858 (pattern : Twelve) (guard : d3256 pattern = 1) : d957 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC855 pattern childGuard
    simpa only [d3256, d957, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC857 pattern childGuard
    simpa only [d3256, d957, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC859 (pattern : Twelve) (guard : d0 pattern = 1) : d949 pattern ≤ (0 : Int) + d3282 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC860 (pattern : Twelve) (guard : d3259 pattern = 1) : d958 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC253 pattern childGuard
    simpa only [d3259, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC859 pattern childGuard
    simpa only [d3259, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC861 (pattern : Twelve) (guard : d3260 pattern = 1) : d964 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d964, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC858 pattern childGuard
    simpa only [d3260, d964, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d964, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC860 pattern childGuard
    simpa only [d3260, d964, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC862 (pattern : Twelve) (guard : d3261 pattern = 1) : d970 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d970, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC853 pattern childGuard
    simpa only [d3261, d970, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d970, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC861 pattern childGuard
    simpa only [d3261, d970, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC863 (pattern : Twelve) (guard : d0 pattern = 1) : d942 pattern ≤ (0 : Int) + d3285 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC864 (pattern : Twelve) (guard : d3255 pattern = 1) : d949 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d3251 pattern = 1 := by simpa only [d3255, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC260 pattern childGuard
    simpa only [d3255, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3255, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC863 pattern childGuard
    simpa only [d3255, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC865 (pattern : Twelve) (guard : d3256 pattern = 1) : d959 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC261 pattern childGuard
    simpa only [d3256, d959, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC864 pattern childGuard
    simpa only [d3256, d959, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC866 (pattern : Twelve) (guard : d0 pattern = 1) : d952 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC867 (pattern : Twelve) (guard : d3259 pattern = 1) : d960 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC267 pattern childGuard
    simpa only [d3259, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC866 pattern childGuard
    simpa only [d3259, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC868 (pattern : Twelve) (guard : d3260 pattern = 1) : d965 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d965, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC865 pattern childGuard
    simpa only [d3260, d965, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d965, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC867 pattern childGuard
    simpa only [d3260, d965, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC869 (pattern : Twelve) (guard : d0 pattern = 1) : d949 pattern ≤ (0 : Int) + d781 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem goalC870 (pattern : Twelve) (guard : d3259 pattern = 1) : d958 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC274 pattern childGuard
    simpa only [d3259, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC869 pattern childGuard
    simpa only [d3259, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC871 (pattern : Twelve) (guard : d3263 pattern = 1) : d966 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d966, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC870 pattern childGuard
    simpa only [d3263, d966, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d966, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3263, d966, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC872 (pattern : Twelve) (guard : d3264 pattern = 1) : d971 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d971, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC868 pattern childGuard
    simpa only [d3264, d971, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d971, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC871 pattern childGuard
    simpa only [d3264, d971, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC873 (pattern : Twelve) (guard : d3265 pattern = 1) : d973 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3265, d973, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC862 pattern childGuard
    simpa only [d3265, d973, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3265, d973, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC872 pattern childGuard
    simpa only [d3265, d973, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC874 (pattern : Twelve) (guard : d3268 pattern = 1) : d974 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range974 pattern).2
  change d974 pattern ≤ (0 : Int) + 6
  omega
theorem goalC875 (pattern : Twelve) (guard : d3269 pattern = 1) : d976 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3269, d976, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC873 pattern childGuard
    simpa only [d3269, d976, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3269, d976, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC874 pattern childGuard
    simpa only [d3269, d976, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC876 (pattern : Twelve) (guard : d3272 pattern = 1) : d977 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range977 pattern).2
  change d977 pattern ≤ (0 : Int) + 6
  omega
theorem goalC877 (pattern : Twelve) (guard : d3273 pattern = 1) : d978 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3273, d978, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC875 pattern childGuard
    simpa only [d3273, d978, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3273, d978, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC876 pattern childGuard
    simpa only [d3273, d978, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC878 (pattern : Twelve) (guard : d3276 pattern = 1) : d977 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range977 pattern).2
  change d977 pattern ≤ (0 : Int) + 6
  omega
theorem goalC879 (pattern : Twelve) (guard : d3277 pattern = 1) : d979 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3277, d979, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC877 pattern childGuard
    simpa only [d3277, d979, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3277, d979, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC878 pattern childGuard
    simpa only [d3277, d979, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC880 (pattern : Twelve) (guard : d3253 pattern = 1) : d980 pattern ≤ (0 : Int) + d26 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3249 pattern = 1 := by simpa only [d3253, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC742 pattern childGuard
    simpa only [d3253, d980, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3253, d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC814 pattern childGuard
    simpa only [d3253, d980, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC881 (pattern : Twelve) (guard : d3256 pattern = 1) : d981 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC758 pattern childGuard
    simpa only [d3256, d981, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC816 pattern childGuard
    simpa only [d3256, d981, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC882 (pattern : Twelve) (guard : d3257 pattern = 1) : d991 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d991, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC880 pattern childGuard
    simpa only [d3257, d991, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d991, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC881 pattern childGuard
    simpa only [d3257, d991, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC883 (pattern : Twelve) (guard : d3256 pattern = 1) : d982 pattern ≤ (0 : Int) + d778 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC767 pattern childGuard
    simpa only [d3256, d982, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC816 pattern childGuard
    simpa only [d3256, d982, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC884 (pattern : Twelve) (guard : d3259 pattern = 1) : d983 pattern ≤ (0 : Int) + d3282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC775 pattern childGuard
    simpa only [d3259, d983, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC184 pattern childGuard
    simpa only [d3259, d983, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC885 (pattern : Twelve) (guard : d3260 pattern = 1) : d992 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d992, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC883 pattern childGuard
    simpa only [d3260, d992, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d992, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC884 pattern childGuard
    simpa only [d3260, d992, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC886 (pattern : Twelve) (guard : d3261 pattern = 1) : d1000 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d1000, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC882 pattern childGuard
    simpa only [d3261, d1000, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d1000, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC885 pattern childGuard
    simpa only [d3261, d1000, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC887 (pattern : Twelve) (guard : d3256 pattern = 1) : d984 pattern ≤ (0 : Int) + d3285 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3252 pattern = 1 := by simpa only [d3256, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC782 pattern childGuard
    simpa only [d3256, d984, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3256, d984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC822 pattern childGuard
    simpa only [d3256, d984, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC888 (pattern : Twelve) (guard : d3259 pattern = 1) : d985 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC789 pattern childGuard
    simpa only [d3259, d985, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC205 pattern childGuard
    simpa only [d3259, d985, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC889 (pattern : Twelve) (guard : d3260 pattern = 1) : d993 pattern ≤ (0 : Int) + d3286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d993, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC887 pattern childGuard
    simpa only [d3260, d993, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d993, d3286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC888 pattern childGuard
    simpa only [d3260, d993, d3286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC890 (pattern : Twelve) (guard : d3259 pattern = 1) : d983 pattern ≤ (0 : Int) + d781 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d3255 pattern = 1 := by simpa only [d3259, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC794 pattern childGuard
    simpa only [d3259, d983, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3259, d983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC205 pattern childGuard
    simpa only [d3259, d983, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC891 (pattern : Twelve) (guard : d3263 pattern = 1) : d994 pattern ≤ (0 : Int) + d3287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3263, d994, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC890 pattern childGuard
    simpa only [d3263, d994, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d3263, d994, d3287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d3263, d994, d3287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC892 (pattern : Twelve) (guard : d3264 pattern = 1) : d1001 pattern ≤ (0 : Int) + d3288 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3264, d1001, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC889 pattern childGuard
    simpa only [d3264, d1001, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3263 pattern = 1 := by simpa only [d3264, d1001, d3288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC891 pattern childGuard
    simpa only [d3264, d1001, d3288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC893 (pattern : Twelve) (guard : d3265 pattern = 1) : d1004 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3265, d1004, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC886 pattern childGuard
    simpa only [d3265, d1004, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3265, d1004, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC892 pattern childGuard
    simpa only [d3265, d1004, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC894 (pattern : Twelve) (guard : d3268 pattern = 1) : d1005 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1005 pattern).2
  change d1005 pattern ≤ (0 : Int) + 6
  omega
theorem goalC895 (pattern : Twelve) (guard : d3269 pattern = 1) : d1007 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3269, d1007, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC893 pattern childGuard
    simpa only [d3269, d1007, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3269, d1007, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC894 pattern childGuard
    simpa only [d3269, d1007, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC896 (pattern : Twelve) (guard : d3272 pattern = 1) : d1008 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1008 pattern).2
  change d1008 pattern ≤ (0 : Int) + 6
  omega
theorem goalC897 (pattern : Twelve) (guard : d3273 pattern = 1) : d1009 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3273, d1009, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC895 pattern childGuard
    simpa only [d3273, d1009, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3273, d1009, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC896 pattern childGuard
    simpa only [d3273, d1009, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC898 (pattern : Twelve) (guard : d3276 pattern = 1) : d1008 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1008 pattern).2
  change d1008 pattern ≤ (0 : Int) + 6
  omega
theorem goalC899 (pattern : Twelve) (guard : d3277 pattern = 1) : d1010 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3277, d1010, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC897 pattern childGuard
    simpa only [d3277, d1010, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3277, d1010, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC898 pattern childGuard
    simpa only [d3277, d1010, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC900 (pattern : Twelve) (guard : d3265 pattern = 1) : d1011 pattern ≤ (0 : Int) + d3289 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d3261 pattern = 1 := by simpa only [d3265, d1011, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC779 pattern childGuard
    simpa only [d3265, d1011, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3264 pattern = 1 := by simpa only [d3265, d1011, d3289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC827 pattern childGuard
    simpa only [d3265, d1011, d3289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC901 (pattern : Twelve) (guard : d3268 pattern = 1) : d1012 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1012 pattern).2
  change d1012 pattern ≤ (0 : Int) + 6
  omega
theorem goalC902 (pattern : Twelve) (guard : d3269 pattern = 1) : d1014 pattern ≤ (0 : Int) + d3290 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d3265 pattern = 1 := by simpa only [d3269, d1014, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC900 pattern childGuard
    simpa only [d3269, d1014, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3268 pattern = 1 := by simpa only [d3269, d1014, d3290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC901 pattern childGuard
    simpa only [d3269, d1014, d3290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC903 (pattern : Twelve) (guard : d3272 pattern = 1) : d1015 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1015 pattern).2
  change d1015 pattern ≤ (0 : Int) + 6
  omega
theorem goalC904 (pattern : Twelve) (guard : d3273 pattern = 1) : d1016 pattern ≤ (0 : Int) + d3291 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d3269 pattern = 1 := by simpa only [d3273, d1016, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC902 pattern childGuard
    simpa only [d3273, d1016, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3272 pattern = 1 := by simpa only [d3273, d1016, d3291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC903 pattern childGuard
    simpa only [d3273, d1016, d3291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC905 (pattern : Twelve) (guard : d3276 pattern = 1) : d1015 pattern ≤ (0 : Int) + d6 pattern := by
  have upper := (range1015 pattern).2
  change d1015 pattern ≤ (0 : Int) + 6
  omega
theorem goalC906 (pattern : Twelve) (guard : d3277 pattern = 1) : d1017 pattern ≤ (0 : Int) + d3292 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d3273 pattern = 1 := by simpa only [d3277, d1017, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC904 pattern childGuard
    simpa only [d3277, d1017, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3276 pattern = 1 := by simpa only [d3277, d1017, d3292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC905 pattern childGuard
    simpa only [d3277, d1017, d3292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC907 (pattern : Twelve) (guard : d3257 pattern = 1) : d1018 pattern ≤ (0 : Int) + d3281 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3253 pattern = 1 := by simpa only [d3257, d1018, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC754 pattern childGuard
    simpa only [d3257, d1018, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3257, d1018, d3281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC817 pattern childGuard
    simpa only [d3257, d1018, d3281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC908 (pattern : Twelve) (guard : d3260 pattern = 1) : d1019 pattern ≤ (0 : Int) + d3283 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d3256 pattern = 1 := by simpa only [d3260, d1019, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC773 pattern childGuard
    simpa only [d3260, d1019, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3259 pattern = 1 := by simpa only [d3260, d1019, d3283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC819 pattern childGuard
    simpa only [d3260, d1019, d3283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem goalC909 (pattern : Twelve) (guard : d3261 pattern = 1) : d1023 pattern ≤ (0 : Int) + d3284 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d3257 pattern = 1 := by simpa only [d3261, d1023, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC907 pattern childGuard
    simpa only [d3261, d1023, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d3260 pattern = 1 := by simpa only [d3261, d1023, d3284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := goalC908 pattern childGuard
    simpa only [d3261, d1023, d3284, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
