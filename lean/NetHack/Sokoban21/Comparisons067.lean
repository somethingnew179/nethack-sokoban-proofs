/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons066
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c9380 (pattern : Twelve) (guard : d1869 pattern = 1) : d862 pattern ≤ (0 : Int) + d1020 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d862, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9378 pattern childGuard
    simpa only [d1869, d862, d1020, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d862, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9379 pattern childGuard
    simpa only [d1869, d862, d1020, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9381 (pattern : Twelve) (guard : d1848 pattern = 1) : d826 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d826, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1918 pattern childGuard
    simpa only [d826, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d826, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5571 pattern childGuard
    simpa only [d826, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9382 (pattern : Twelve) (guard : d1848 pattern = 1) : d840 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d840, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9290 pattern childGuard
    simpa only [d840, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d840, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9381 pattern childGuard
    simpa only [d840, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9383 (pattern : Twelve) (guard : d1848 pattern = 1) : d827 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1922 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5109 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9384 (pattern : Twelve) (guard : d1848 pattern = 1) : d841 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d841, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9383 pattern childGuard
    simpa only [d841, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d841, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4693 pattern childGuard
    simpa only [d841, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9385 (pattern : Twelve) (guard : d1848 pattern = 1) : d854 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d854, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9382 pattern childGuard
    simpa only [d854, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d854, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9384 pattern childGuard
    simpa only [d854, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9386 (pattern : Twelve) (guard : d1869 pattern = 1) : d863 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d863, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9385 pattern childGuard
    simpa only [d1869, d863, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d863, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d863, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9387 (pattern : Twelve) (guard : d1869 pattern = 1) : d867 pattern ≤ (0 : Int) + d1024 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d867, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9380 pattern childGuard
    simpa only [d867, d1024, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d867, d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9386 pattern childGuard
    simpa only [d867, d1024, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9388 (pattern : Twelve) (guard : d1869 pattern = 1) : d869 pattern ≤ (0 : Int) + d1025 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d869, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9373 pattern childGuard
    simpa only [d869, d1025, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d869, d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9387 pattern childGuard
    simpa only [d869, d1025, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9389 (pattern : Twelve) (guard : d1848 pattern = 1) : d839 pattern ≤ (0 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6868 pattern childGuard
    simpa only [d839, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4693 pattern childGuard
    simpa only [d839, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9390 (pattern : Twelve) (guard : d1848 pattern = 1) : d853 pattern ≤ (0 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4706 pattern childGuard
    simpa only [d853, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9389 pattern childGuard
    simpa only [d853, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9391 (pattern : Twelve) (guard : d1869 pattern = 1) : d861 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d861, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9390 pattern childGuard
    simpa only [d1869, d861, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d861, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c771 pattern childGuard
    simpa only [d1869, d861, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9392 (pattern : Twelve) (guard : d1848 pattern = 1) : d843 pattern ≤ (0 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d843, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1941 pattern childGuard
    simpa only [d843, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d843, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4693 pattern childGuard
    simpa only [d843, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9393 (pattern : Twelve) (guard : d1848 pattern = 1) : d855 pattern ≤ (0 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d855, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9376 pattern childGuard
    simpa only [d855, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d855, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9392 pattern childGuard
    simpa only [d855, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9394 (pattern : Twelve) (guard : d0 pattern = 1) : d856 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9395 (pattern : Twelve) (guard : d1869 pattern = 1) : d862 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d862, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9393 pattern childGuard
    simpa only [d1869, d862, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d862, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9394 pattern childGuard
    simpa only [d1869, d862, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9396 (pattern : Twelve) (guard : d1848 pattern = 1) : d827 pattern ≤ (0 : Int) + d823 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1941 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5132 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9397 (pattern : Twelve) (guard : d1848 pattern = 1) : d841 pattern ≤ (0 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d841, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9396 pattern childGuard
    simpa only [d841, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d841, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4693 pattern childGuard
    simpa only [d841, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9398 (pattern : Twelve) (guard : d1848 pattern = 1) : d854 pattern ≤ (0 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d854, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9382 pattern childGuard
    simpa only [d854, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d854, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9397 pattern childGuard
    simpa only [d854, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9399 (pattern : Twelve) (guard : d1869 pattern = 1) : d863 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d863, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9398 pattern childGuard
    simpa only [d1869, d863, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d863, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d863, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9400 (pattern : Twelve) (guard : d1869 pattern = 1) : d867 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9395 pattern childGuard
    simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9399 pattern childGuard
    simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9401 (pattern : Twelve) (guard : d1869 pattern = 1) : d869 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9391 pattern childGuard
    simpa only [d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9400 pattern childGuard
    simpa only [d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9402 (pattern : Twelve) (guard : d1869 pattern = 1) : d869 pattern ≤ (0 : Int) + d1026 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9388 pattern childGuard
    simpa only [d1026, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9401 pattern childGuard
    simpa only [d1026, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9403 (pattern : Twelve) (guard : d1869 pattern = 1) : d861 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d861, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4686 pattern childGuard
    simpa only [d1869, d861, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d861, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c771 pattern childGuard
    simpa only [d1869, d861, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9404 (pattern : Twelve) (guard : d1869 pattern = 1) : d862 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d862, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9378 pattern childGuard
    simpa only [d1869, d862, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d862, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9394 pattern childGuard
    simpa only [d1869, d862, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9405 (pattern : Twelve) (guard : d1869 pattern = 1) : d867 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9404 pattern childGuard
    simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9386 pattern childGuard
    simpa only [d867, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9406 (pattern : Twelve) (guard : d1869 pattern = 1) : d869 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9403 pattern childGuard
    simpa only [d869, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9405 pattern childGuard
    simpa only [d869, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9407 (pattern : Twelve) (guard : d1869 pattern = 1) : d869 pattern ≤ (0 : Int) + d1027 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9406 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9401 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9408 (pattern : Twelve) (guard : d1869 pattern = 1) : d869 pattern ≤ (0 : Int) + d1028 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9402 pattern childGuard
    simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9407 pattern childGuard
    simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9409 (pattern : Twelve) (guard : d0 pattern = 1) : d872 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9410 (pattern : Twelve) (guard : d1848 pattern = 1) : d874 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d874, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d874, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d874, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9409 pattern childGuard
    simpa only [d1848, d874, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9411 (pattern : Twelve) (guard : d1848 pattern = 1) : d875 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d875, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d1848, d875, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d875, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9409 pattern childGuard
    simpa only [d1848, d875, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9412 (pattern : Twelve) (guard : d1848 pattern = 1) : d882 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d882, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9410 pattern childGuard
    simpa only [d882, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d882, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9411 pattern childGuard
    simpa only [d882, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9413 (pattern : Twelve) (guard : d1848 pattern = 1) : d890 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d890, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d890, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d890, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9412 pattern childGuard
    simpa only [d890, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9414 (pattern : Twelve) (guard : d1848 pattern = 1) : d876 pattern ≤ (0 : Int) + d817 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d876, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d876, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d876, d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2015 pattern childGuard
    simpa only [d1848, d876, d817, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9415 (pattern : Twelve) (guard : d1848 pattern = 1) : d883 pattern ≤ (0 : Int) + d825 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d883, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9414 pattern childGuard
    simpa only [d883, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d883, d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2806 pattern childGuard
    simpa only [d883, d825, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9416 (pattern : Twelve) (guard : d1848 pattern = 1) : d891 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d891, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1670 pattern childGuard
    simpa only [d891, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d891, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9415 pattern childGuard
    simpa only [d891, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9417 (pattern : Twelve) (guard : d1848 pattern = 1) : d898 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d898, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9413 pattern childGuard
    simpa only [d898, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d898, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9416 pattern childGuard
    simpa only [d898, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9418 (pattern : Twelve) (guard : d0 pattern = 1) : d899 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9419 (pattern : Twelve) (guard : d1869 pattern = 1) : d902 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d902, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9417 pattern childGuard
    simpa only [d1869, d902, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d902, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9418 pattern childGuard
    simpa only [d1869, d902, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9420 (pattern : Twelve) (guard : d0 pattern = 1) : d815 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9421 (pattern : Twelve) (guard : d1848 pattern = 1) : d877 pattern ≤ (0 : Int) + d27 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d877, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d877, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d877, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9420 pattern childGuard
    simpa only [d1848, d877, d27, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9422 (pattern : Twelve) (guard : d0 pattern = 1) : d24 pattern ≤ (0 : Int) + d1 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9423 (pattern : Twelve) (guard : d1848 pattern = 1) : d878 pattern ≤ (0 : Int) + d816 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d878, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d1848, d878, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d878, d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9422 pattern childGuard
    simpa only [d1848, d878, d816, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9424 (pattern : Twelve) (guard : d1848 pattern = 1) : d885 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d885, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9421 pattern childGuard
    simpa only [d885, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d885, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9423 pattern childGuard
    simpa only [d885, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9425 (pattern : Twelve) (guard : d1848 pattern = 1) : d894 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d894, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1610 pattern childGuard
    simpa only [d894, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d894, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9424 pattern childGuard
    simpa only [d894, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9426 (pattern : Twelve) (guard : d0 pattern = 1) : d119 pattern ≤ (0 : Int) + d17 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9427 (pattern : Twelve) (guard : d1848 pattern = 1) : d879 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9426 pattern childGuard
    simpa only [d1848, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9428 (pattern : Twelve) (guard : d1848 pattern = 1) : d886 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1922 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9427 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9429 (pattern : Twelve) (guard : d1848 pattern = 1) : d895 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d895, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9428 pattern childGuard
    simpa only [d895, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d895, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9415 pattern childGuard
    simpa only [d895, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9430 (pattern : Twelve) (guard : d1848 pattern = 1) : d900 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d900, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9425 pattern childGuard
    simpa only [d900, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d900, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9429 pattern childGuard
    simpa only [d900, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9431 (pattern : Twelve) (guard : d0 pattern = 1) : d901 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9432 (pattern : Twelve) (guard : d1869 pattern = 1) : d903 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d903, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9430 pattern childGuard
    simpa only [d1869, d903, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d903, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9431 pattern childGuard
    simpa only [d1869, d903, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9433 (pattern : Twelve) (guard : d1848 pattern = 1) : d884 pattern ≤ (0 : Int) + d824 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d884, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9421 pattern childGuard
    simpa only [d884, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d884, d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5571 pattern childGuard
    simpa only [d884, d824, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9434 (pattern : Twelve) (guard : d1848 pattern = 1) : d892 pattern ≤ (0 : Int) + d838 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d892, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9290 pattern childGuard
    simpa only [d892, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d892, d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9433 pattern childGuard
    simpa only [d892, d838, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9435 (pattern : Twelve) (guard : d1848 pattern = 1) : d893 pattern ≤ (0 : Int) + d839 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d893, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9383 pattern childGuard
    simpa only [d893, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d893, d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9415 pattern childGuard
    simpa only [d893, d839, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9436 (pattern : Twelve) (guard : d1848 pattern = 1) : d899 pattern ≤ (0 : Int) + d853 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d899, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9434 pattern childGuard
    simpa only [d899, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d899, d853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9435 pattern childGuard
    simpa only [d899, d853, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9437 (pattern : Twelve) (guard : d1869 pattern = 1) : d904 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d904, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9436 pattern childGuard
    simpa only [d1869, d904, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d904, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d904, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9438 (pattern : Twelve) (guard : d1869 pattern = 1) : d905 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9432 pattern childGuard
    simpa only [d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9437 pattern childGuard
    simpa only [d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9439 (pattern : Twelve) (guard : d1869 pattern = 1) : d906 pattern ≤ (0 : Int) + d1021 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9419 pattern childGuard
    simpa only [d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9438 pattern childGuard
    simpa only [d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9440 (pattern : Twelve) (guard : d1848 pattern = 1) : d891 pattern ≤ (0 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d891, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6868 pattern childGuard
    simpa only [d891, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d891, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9415 pattern childGuard
    simpa only [d891, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9441 (pattern : Twelve) (guard : d1848 pattern = 1) : d898 pattern ≤ (0 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d898, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9413 pattern childGuard
    simpa only [d898, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d898, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9440 pattern childGuard
    simpa only [d898, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9442 (pattern : Twelve) (guard : d1869 pattern = 1) : d902 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d902, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9441 pattern childGuard
    simpa only [d1869, d902, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d902, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9418 pattern childGuard
    simpa only [d1869, d902, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9443 (pattern : Twelve) (guard : d0 pattern = 1) : d119 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9444 (pattern : Twelve) (guard : d1848 pattern = 1) : d879 pattern ≤ (0 : Int) + d823 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d879, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d879, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d879, d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9443 pattern childGuard
    simpa only [d1848, d879, d823, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9445 (pattern : Twelve) (guard : d1848 pattern = 1) : d886 pattern ≤ (0 : Int) + d823 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1941 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9444 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9446 (pattern : Twelve) (guard : d1848 pattern = 1) : d895 pattern ≤ (0 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d895, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9445 pattern childGuard
    simpa only [d895, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d895, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9415 pattern childGuard
    simpa only [d895, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9447 (pattern : Twelve) (guard : d1848 pattern = 1) : d900 pattern ≤ (0 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d900, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9425 pattern childGuard
    simpa only [d900, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d900, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9446 pattern childGuard
    simpa only [d900, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9448 (pattern : Twelve) (guard : d1869 pattern = 1) : d903 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d903, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9447 pattern childGuard
    simpa only [d1869, d903, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d903, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9431 pattern childGuard
    simpa only [d1869, d903, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9449 (pattern : Twelve) (guard : d1848 pattern = 1) : d893 pattern ≤ (0 : Int) + d846 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d893, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9396 pattern childGuard
    simpa only [d893, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d893, d846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9415 pattern childGuard
    simpa only [d893, d846, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9450 (pattern : Twelve) (guard : d1848 pattern = 1) : d899 pattern ≤ (0 : Int) + d857 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d899, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9434 pattern childGuard
    simpa only [d899, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d899, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9449 pattern childGuard
    simpa only [d899, d857, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9451 (pattern : Twelve) (guard : d1869 pattern = 1) : d904 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d904, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9450 pattern childGuard
    simpa only [d1869, d904, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d904, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d904, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9452 (pattern : Twelve) (guard : d1869 pattern = 1) : d905 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9448 pattern childGuard
    simpa only [d905, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9451 pattern childGuard
    simpa only [d905, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9453 (pattern : Twelve) (guard : d1869 pattern = 1) : d906 pattern ≤ (0 : Int) + d1022 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9442 pattern childGuard
    simpa only [d906, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9452 pattern childGuard
    simpa only [d906, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9454 (pattern : Twelve) (guard : d1869 pattern = 1) : d906 pattern ≤ (0 : Int) + d1027 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9439 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9453 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9455 (pattern : Twelve) (guard : d1869 pattern = 1) : d907 pattern ≤ (0 : Int) + d1029 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d907, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9408 pattern childGuard
    simpa only [d907, d1029, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d907, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9454 pattern childGuard
    simpa only [d907, d1029, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9456 (pattern : Twelve) (guard : d1869 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1435 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1313, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4774 pattern childGuard
    simpa only [d1869, d1313, d1435, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1313, d1435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c781 pattern childGuard
    simpa only [d1869, d1313, d1435, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9457 (pattern : Twelve) (guard : d1869 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1313, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4774 pattern childGuard
    simpa only [d1869, d1313, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1313, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c795 pattern childGuard
    simpa only [d1869, d1313, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9458 (pattern : Twelve) (guard : d1869 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1438 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9456 pattern childGuard
    simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9457 pattern childGuard
    simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9459 (pattern : Twelve) (guard : d0 pattern = 1) : d119 pattern ≤ (0 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9460 (pattern : Twelve) (guard : d1848 pattern = 1) : d1281 pattern ≤ (0 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4265 pattern childGuard
    simpa only [d1848, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9459 pattern childGuard
    simpa only [d1848, d1281, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9461 (pattern : Twelve) (guard : d1848 pattern = 1) : d1287 pattern ≤ (0 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1287, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1972 pattern childGuard
    simpa only [d1287, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1287, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9460 pattern childGuard
    simpa only [d1287, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9462 (pattern : Twelve) (guard : d1848 pattern = 1) : d1297 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1297, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1922 pattern childGuard
    simpa only [d1297, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1297, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9461 pattern childGuard
    simpa only [d1297, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9463 (pattern : Twelve) (guard : d1848 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1298, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1976 pattern childGuard
    simpa only [d1298, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1298, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1298, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9464 (pattern : Twelve) (guard : d1848 pattern = 1) : d1307 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1307, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9462 pattern childGuard
    simpa only [d1307, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1307, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9463 pattern childGuard
    simpa only [d1307, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9465 (pattern : Twelve) (guard : d0 pattern = 1) : d1308 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9466 (pattern : Twelve) (guard : d1869 pattern = 1) : d1314 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1314, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9464 pattern childGuard
    simpa only [d1869, d1314, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1314, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9465 pattern childGuard
    simpa only [d1869, d1314, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9467 (pattern : Twelve) (guard : d1848 pattern = 1) : d1285 pattern ≤ (0 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1285, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1972 pattern childGuard
    simpa only [d1285, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1285, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5647 pattern childGuard
    simpa only [d1285, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9468 (pattern : Twelve) (guard : d1848 pattern = 1) : d1295 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1295, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9383 pattern childGuard
    simpa only [d1295, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1295, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9467 pattern childGuard
    simpa only [d1295, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9469 (pattern : Twelve) (guard : d1848 pattern = 1) : d1286 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1976 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5162 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9470 (pattern : Twelve) (guard : d1848 pattern = 1) : d1296 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1296, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9469 pattern childGuard
    simpa only [d1296, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1296, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1296, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9471 (pattern : Twelve) (guard : d1848 pattern = 1) : d1306 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1306, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9468 pattern childGuard
    simpa only [d1306, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1306, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9470 pattern childGuard
    simpa only [d1306, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9472 (pattern : Twelve) (guard : d1869 pattern = 1) : d1315 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1315, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9471 pattern childGuard
    simpa only [d1869, d1315, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1315, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1315, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9473 (pattern : Twelve) (guard : d1869 pattern = 1) : d1319 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9466 pattern childGuard
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9472 pattern childGuard
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9474 (pattern : Twelve) (guard : d1869 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1439 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1321, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9458 pattern childGuard
    simpa only [d1321, d1439, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1321, d1439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9473 pattern childGuard
    simpa only [d1321, d1439, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9475 (pattern : Twelve) (guard : d1848 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1294, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c6928 pattern childGuard
    simpa only [d1294, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1294, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1294, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9476 (pattern : Twelve) (guard : d1848 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4794 pattern childGuard
    simpa only [d1305, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9475 pattern childGuard
    simpa only [d1305, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9477 (pattern : Twelve) (guard : d1869 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1313, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9476 pattern childGuard
    simpa only [d1869, d1313, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1313, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c795 pattern childGuard
    simpa only [d1869, d1313, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9478 (pattern : Twelve) (guard : d1848 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1298, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1991 pattern childGuard
    simpa only [d1298, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1298, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1298, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9479 (pattern : Twelve) (guard : d1848 pattern = 1) : d1307 pattern ≤ (0 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1307, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9462 pattern childGuard
    simpa only [d1307, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1307, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9478 pattern childGuard
    simpa only [d1307, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9480 (pattern : Twelve) (guard : d1869 pattern = 1) : d1314 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1314, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9479 pattern childGuard
    simpa only [d1869, d1314, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1314, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9465 pattern childGuard
    simpa only [d1869, d1314, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9481 (pattern : Twelve) (guard : d1848 pattern = 1) : d1286 pattern ≤ (0 : Int) + d1283 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1991 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5189 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9482 (pattern : Twelve) (guard : d1848 pattern = 1) : d1296 pattern ≤ (0 : Int) + d1301 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1296, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9481 pattern childGuard
    simpa only [d1296, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1296, d1301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1296, d1301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9483 (pattern : Twelve) (guard : d1848 pattern = 1) : d1306 pattern ≤ (0 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1306, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9468 pattern childGuard
    simpa only [d1306, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1306, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9482 pattern childGuard
    simpa only [d1306, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9484 (pattern : Twelve) (guard : d1869 pattern = 1) : d1315 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1315, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9483 pattern childGuard
    simpa only [d1869, d1315, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1315, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1315, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9485 (pattern : Twelve) (guard : d1869 pattern = 1) : d1319 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9480 pattern childGuard
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9484 pattern childGuard
    simpa only [d1319, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9486 (pattern : Twelve) (guard : d1869 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9477 pattern childGuard
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9485 pattern childGuard
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9487 (pattern : Twelve) (guard : d1869 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1440 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9474 pattern childGuard
    simpa only [d1440, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9486 pattern childGuard
    simpa only [d1440, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9488 (pattern : Twelve) (guard : d1869 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9457 pattern childGuard
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9473 pattern childGuard
    simpa only [d1321, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9489 (pattern : Twelve) (guard : d1869 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1441 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9488 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9486 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9490 (pattern : Twelve) (guard : d1869 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1442 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9487 pattern childGuard
    simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9489 pattern childGuard
    simpa only [d1442, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9491 (pattern : Twelve) (guard : d0 pattern = 1) : d1324 pattern ≤ (0 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9492 (pattern : Twelve) (guard : d1848 pattern = 1) : d1325 pattern ≤ (0 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1325, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1469 pattern childGuard
    simpa only [d1848, d1325, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1325, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9491 pattern childGuard
    simpa only [d1848, d1325, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9493 (pattern : Twelve) (guard : d1848 pattern = 1) : d1326 pattern ≤ (0 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4265 pattern childGuard
    simpa only [d1848, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9491 pattern childGuard
    simpa only [d1848, d1326, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9494 (pattern : Twelve) (guard : d1848 pattern = 1) : d1333 pattern ≤ (0 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1333, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9492 pattern childGuard
    simpa only [d1333, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1333, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9493 pattern childGuard
    simpa only [d1333, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9495 (pattern : Twelve) (guard : d1848 pattern = 1) : d1339 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1339, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1670 pattern childGuard
    simpa only [d1339, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1339, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9494 pattern childGuard
    simpa only [d1339, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9496 (pattern : Twelve) (guard : d1848 pattern = 1) : d1345 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1345, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9495 pattern childGuard
    simpa only [d1345, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1345, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4816 pattern childGuard
    simpa only [d1345, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9497 (pattern : Twelve) (guard : d0 pattern = 1) : d1346 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9498 (pattern : Twelve) (guard : d1869 pattern = 1) : d1349 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1349, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9496 pattern childGuard
    simpa only [d1869, d1349, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1349, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9497 pattern childGuard
    simpa only [d1869, d1349, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9499 (pattern : Twelve) (guard : d1848 pattern = 1) : d1327 pattern ≤ (0 : Int) + d1278 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1327, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1469 pattern childGuard
    simpa only [d1848, d1327, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1327, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9459 pattern childGuard
    simpa only [d1848, d1327, d1278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9500 (pattern : Twelve) (guard : d0 pattern = 1) : d1277 pattern ≤ (0 : Int) + d872 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9501 (pattern : Twelve) (guard : d1848 pattern = 1) : d1328 pattern ≤ (0 : Int) + d872 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4265 pattern childGuard
    simpa only [d1848, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9500 pattern childGuard
    simpa only [d1848, d1328, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9502 (pattern : Twelve) (guard : d1848 pattern = 1) : d1335 pattern ≤ (0 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1335, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9499 pattern childGuard
    simpa only [d1335, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1335, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9501 pattern childGuard
    simpa only [d1335, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9503 (pattern : Twelve) (guard : d1848 pattern = 1) : d1341 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1341, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1922 pattern childGuard
    simpa only [d1341, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1341, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9502 pattern childGuard
    simpa only [d1341, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9504 (pattern : Twelve) (guard : d0 pattern = 1) : d20 pattern ≤ (0 : Int) + d19 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9505 (pattern : Twelve) (guard : d1848 pattern = 1) : d1329 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9504 pattern childGuard
    simpa only [d1848, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9506 (pattern : Twelve) (guard : d1848 pattern = 1) : d1336 pattern ≤ (0 : Int) + d19 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1976 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9505 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9507 (pattern : Twelve) (guard : d1848 pattern = 1) : d1342 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1342, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9506 pattern childGuard
    simpa only [d1342, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1342, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1342, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9508 (pattern : Twelve) (guard : d1848 pattern = 1) : d1347 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1347, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9503 pattern childGuard
    simpa only [d1347, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1347, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9507 pattern childGuard
    simpa only [d1347, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9509 (pattern : Twelve) (guard : d0 pattern = 1) : d1348 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c9510 (pattern : Twelve) (guard : d1869 pattern = 1) : d1350 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1350, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9508 pattern childGuard
    simpa only [d1869, d1350, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1350, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9509 pattern childGuard
    simpa only [d1869, d1350, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9511 (pattern : Twelve) (guard : d1848 pattern = 1) : d1334 pattern ≤ (0 : Int) + d1284 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1334, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9499 pattern childGuard
    simpa only [d1334, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1334, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5647 pattern childGuard
    simpa only [d1334, d1284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9512 (pattern : Twelve) (guard : d1848 pattern = 1) : d1340 pattern ≤ (0 : Int) + d1293 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1340, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9383 pattern childGuard
    simpa only [d1340, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1340, d1293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9511 pattern childGuard
    simpa only [d1340, d1293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9513 (pattern : Twelve) (guard : d1848 pattern = 1) : d1346 pattern ≤ (0 : Int) + d1305 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1346, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9512 pattern childGuard
    simpa only [d1346, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1346, d1305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9470 pattern childGuard
    simpa only [d1346, d1305, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9514 (pattern : Twelve) (guard : d1869 pattern = 1) : d1351 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1351, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9513 pattern childGuard
    simpa only [d1869, d1351, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1351, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1351, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9515 (pattern : Twelve) (guard : d1869 pattern = 1) : d1352 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9510 pattern childGuard
    simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9514 pattern childGuard
    simpa only [d1352, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9516 (pattern : Twelve) (guard : d1869 pattern = 1) : d1353 pattern ≤ (0 : Int) + d1436 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9498 pattern childGuard
    simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9515 pattern childGuard
    simpa only [d1353, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9517 (pattern : Twelve) (guard : d1848 pattern = 1) : d1345 pattern ≤ (0 : Int) + d1309 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1345, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9495 pattern childGuard
    simpa only [d1345, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1345, d1309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9475 pattern childGuard
    simpa only [d1345, d1309, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9518 (pattern : Twelve) (guard : d1869 pattern = 1) : d1349 pattern ≤ (0 : Int) + d1437 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1349, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9517 pattern childGuard
    simpa only [d1869, d1349, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1349, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c9497 pattern childGuard
    simpa only [d1869, d1349, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c9519 (pattern : Twelve) (guard : d0 pattern = 1) : d20 pattern ≤ (0 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban21.Diagram
