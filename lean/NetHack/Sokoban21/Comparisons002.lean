/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons001
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c280 (pattern : Twelve) (guard : d1837 pattern = 1) : d831 pattern ≤ (0 : Int) + d945 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d831, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c278 pattern childGuard
    simpa only [d1837, d831, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d831, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c279 pattern childGuard
    simpa only [d1837, d831, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c281 (pattern : Twelve) (guard : d1837 pattern = 1) : d845 pattern ≤ (0 : Int) + d952 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d845, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c277 pattern childGuard
    simpa only [d845, d952, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d845, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c280 pattern childGuard
    simpa only [d845, d952, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c282 (pattern : Twelve) (guard : d1837 pattern = 1) : d856 pattern ≤ (0 : Int) + d960 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d856, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c276 pattern childGuard
    simpa only [d856, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d856, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c281 pattern childGuard
    simpa only [d856, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c283 (pattern : Twelve) (guard : d1837 pattern = 1) : d862 pattern ≤ (0 : Int) + d965 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d862, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c273 pattern childGuard
    simpa only [d862, d965, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d862, d965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c282 pattern childGuard
    simpa only [d862, d965, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c284 (pattern : Twelve) (guard : d1837 pattern = 1) : d863 pattern ≤ (0 : Int) + d966 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d863, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c264 pattern childGuard
    simpa only [d863, d966, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d863, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d863, d966, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c285 (pattern : Twelve) (guard : d1837 pattern = 1) : d867 pattern ≤ (0 : Int) + d971 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d867, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c283 pattern childGuard
    simpa only [d867, d971, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d867, d971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c284 pattern childGuard
    simpa only [d867, d971, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c286 (pattern : Twelve) (guard : d1837 pattern = 1) : d869 pattern ≤ (0 : Int) + d973 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d869, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c266 pattern childGuard
    simpa only [d869, d973, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d869, d973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c285 pattern childGuard
    simpa only [d869, d973, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c287 (pattern : Twelve) (guard : d1837 pattern = 1) : d838 pattern ≤ (0 : Int) + d953 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d838, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c158 pattern childGuard
    simpa only [d838, d953, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d838, d953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c257 pattern childGuard
    simpa only [d838, d953, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c288 (pattern : Twelve) (guard : d1 pattern = 1) : d823 pattern ≤ (0 : Int) + d823 pattern := by
  omega
theorem c289 (pattern : Twelve) (guard : d0 pattern = 1) : d823 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c290 (pattern : Twelve) (guard : d1837 pattern = 1) : d823 pattern ≤ (0 : Int) + d946 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c288 pattern childGuard
    simpa only [d1837, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c289 pattern childGuard
    simpa only [d1837, d946, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c291 (pattern : Twelve) (guard : d1837 pattern = 1) : d846 pattern ≤ (0 : Int) + d954 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d846, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c290 pattern childGuard
    simpa only [d846, d954, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d846, d954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c244 pattern childGuard
    simpa only [d846, d954, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c292 (pattern : Twelve) (guard : d1837 pattern = 1) : d857 pattern ≤ (0 : Int) + d961 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d857, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c287 pattern childGuard
    simpa only [d857, d961, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d857, d961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c291 pattern childGuard
    simpa only [d857, d961, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c293 (pattern : Twelve) (guard : d1837 pattern = 1) : d832 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d832, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d832, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d832, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c177 pattern childGuard
    simpa only [d1837, d832, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c294 (pattern : Twelve) (guard : d1837 pattern = 1) : d847 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d847, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c121 pattern childGuard
    simpa only [d847, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d847, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c293 pattern childGuard
    simpa only [d847, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c295 (pattern : Twelve) (guard : d1837 pattern = 1) : d833 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d833, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d833, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d833, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c141 pattern childGuard
    simpa only [d1837, d833, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c296 (pattern : Twelve) (guard : d1837 pattern = 1) : d848 pattern ≤ (0 : Int) + d949 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d848, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c295 pattern childGuard
    simpa only [d848, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d848, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c244 pattern childGuard
    simpa only [d848, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c297 (pattern : Twelve) (guard : d1837 pattern = 1) : d858 pattern ≤ (0 : Int) + d958 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d858, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c294 pattern childGuard
    simpa only [d858, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d858, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c296 pattern childGuard
    simpa only [d858, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c298 (pattern : Twelve) (guard : d1837 pattern = 1) : d864 pattern ≤ (0 : Int) + d967 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d864, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c292 pattern childGuard
    simpa only [d864, d967, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d864, d967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c297 pattern childGuard
    simpa only [d864, d967, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c299 (pattern : Twelve) (guard : d1837 pattern = 1) : d834 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d834, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d834, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d834, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c185 pattern childGuard
    simpa only [d1837, d834, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c300 (pattern : Twelve) (guard : d1837 pattern = 1) : d849 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d849, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c163 pattern childGuard
    simpa only [d849, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d849, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c299 pattern childGuard
    simpa only [d849, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c301 (pattern : Twelve) (guard : d1837 pattern = 1) : d835 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d835, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c100 pattern childGuard
    simpa only [d1837, d835, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d835, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c188 pattern childGuard
    simpa only [d1837, d835, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c302 (pattern : Twelve) (guard : d1837 pattern = 1) : d850 pattern ≤ (0 : Int) + d949 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d850, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c301 pattern childGuard
    simpa only [d850, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d850, d949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c244 pattern childGuard
    simpa only [d850, d949, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c303 (pattern : Twelve) (guard : d1837 pattern = 1) : d859 pattern ≤ (0 : Int) + d958 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d859, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c300 pattern childGuard
    simpa only [d859, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d859, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c302 pattern childGuard
    simpa only [d859, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c304 (pattern : Twelve) (guard : d1837 pattern = 1) : d836 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d836, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c143 pattern childGuard
    simpa only [d1837, d836, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d836, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c192 pattern childGuard
    simpa only [d1837, d836, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c305 (pattern : Twelve) (guard : d1837 pattern = 1) : d851 pattern ≤ (0 : Int) + d267 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d851, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c142 pattern childGuard
    simpa only [d851, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d851, d267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c304 pattern childGuard
    simpa only [d851, d267, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c306 (pattern : Twelve) (guard : d1837 pattern = 1) : d837 pattern ≤ (0 : Int) + d251 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d837, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c143 pattern childGuard
    simpa only [d1837, d837, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d837, d251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c195 pattern childGuard
    simpa only [d1837, d837, d251, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c307 (pattern : Twelve) (guard : d1837 pattern = 1) : d852 pattern ≤ (0 : Int) + d952 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d852, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c306 pattern childGuard
    simpa only [d852, d952, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d852, d952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c280 pattern childGuard
    simpa only [d852, d952, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c308 (pattern : Twelve) (guard : d1837 pattern = 1) : d860 pattern ≤ (0 : Int) + d960 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d860, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c305 pattern childGuard
    simpa only [d860, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d860, d960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c307 pattern childGuard
    simpa only [d860, d960, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c309 (pattern : Twelve) (guard : d1837 pattern = 1) : d865 pattern ≤ (0 : Int) + d968 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d865, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c303 pattern childGuard
    simpa only [d865, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d865, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c308 pattern childGuard
    simpa only [d865, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c310 (pattern : Twelve) (guard : d1837 pattern = 1) : d866 pattern ≤ (0 : Int) + d966 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d866, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c297 pattern childGuard
    simpa only [d866, d966, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d866, d966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d866, d966, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c311 (pattern : Twelve) (guard : d1837 pattern = 1) : d868 pattern ≤ (0 : Int) + d972 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d868, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c309 pattern childGuard
    simpa only [d868, d972, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d868, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c310 pattern childGuard
    simpa only [d868, d972, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c312 (pattern : Twelve) (guard : d1837 pattern = 1) : d870 pattern ≤ (0 : Int) + d974 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d870, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c298 pattern childGuard
    simpa only [d870, d974, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d870, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c311 pattern childGuard
    simpa only [d870, d974, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c313 (pattern : Twelve) (guard : d1837 pattern = 1) : d871 pattern ≤ (0 : Int) + d976 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d871, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c286 pattern childGuard
    simpa only [d871, d976, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d871, d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c312 pattern childGuard
    simpa only [d871, d976, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c314 (pattern : Twelve) (guard : d1837 pattern = 1) : d853 pattern ≤ (0 : Int) + d962 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d853, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c287 pattern childGuard
    simpa only [d853, d962, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d853, d962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c261 pattern childGuard
    simpa only [d853, d962, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c315 (pattern : Twelve) (guard : d1837 pattern = 1) : d861 pattern ≤ (0 : Int) + d969 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d861, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c314 pattern childGuard
    simpa only [d861, d969, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d861, d969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c264 pattern childGuard
    simpa only [d861, d969, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c316 (pattern : Twelve) (guard : d1837 pattern = 1) : d842 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d842, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c163 pattern childGuard
    simpa only [d842, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d842, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c268 pattern childGuard
    simpa only [d842, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c317 (pattern : Twelve) (guard : d1837 pattern = 1) : d855 pattern ≤ (0 : Int) + d958 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d855, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c316 pattern childGuard
    simpa only [d855, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d855, d958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c272 pattern childGuard
    simpa only [d855, d958, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c318 (pattern : Twelve) (guard : d1837 pattern = 1) : d862 pattern ≤ (0 : Int) + d968 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d862, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c317 pattern childGuard
    simpa only [d862, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d862, d968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c282 pattern childGuard
    simpa only [d862, d968, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c319 (pattern : Twelve) (guard : d1837 pattern = 1) : d867 pattern ≤ (0 : Int) + d972 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d867, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c318 pattern childGuard
    simpa only [d867, d972, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d867, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c284 pattern childGuard
    simpa only [d867, d972, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c320 (pattern : Twelve) (guard : d1837 pattern = 1) : d869 pattern ≤ (0 : Int) + d975 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d869, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c315 pattern childGuard
    simpa only [d869, d975, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d869, d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c319 pattern childGuard
    simpa only [d869, d975, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c321 (pattern : Twelve) (guard : d1837 pattern = 1) : d871 pattern ≤ (0 : Int) + d977 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d871, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c320 pattern childGuard
    simpa only [d871, d977, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d871, d977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c312 pattern childGuard
    simpa only [d871, d977, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c322 (pattern : Twelve) (guard : d1837 pattern = 1) : d871 pattern ≤ (0 : Int) + d978 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c313 pattern childGuard
    simpa only [d978, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c321 pattern childGuard
    simpa only [d978, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c323 (pattern : Twelve) (guard : d1837 pattern = 1) : d871 pattern ≤ (0 : Int) + d979 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c322 pattern childGuard
    simpa only [d979, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c321 pattern childGuard
    simpa only [d979, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c324 (pattern : Twelve) (guard : d1 pattern = 1) : d1278 pattern ≤ (0 : Int) + d1278 pattern := by
  omega
theorem c325 (pattern : Twelve) (guard : d0 pattern = 1) : d872 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c326 (pattern : Twelve) (guard : d1837 pattern = 1) : d1284 pattern ≤ (0 : Int) + d1380 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1284, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c324 pattern childGuard
    simpa only [d1837, d1284, d1380, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1284, d1380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c325 pattern childGuard
    simpa only [d1837, d1284, d1380, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c327 (pattern : Twelve) (guard : d1837 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1385 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1293, d1385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c242 pattern childGuard
    simpa only [d1293, d1385, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1293, d1385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c326 pattern childGuard
    simpa only [d1293, d1385, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c328 (pattern : Twelve) (guard : d1 pattern = 1) : d19 pattern ≤ (0 : Int) + d19 pattern := by
  omega
theorem c329 (pattern : Twelve) (guard : d0 pattern = 1) : d19 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c330 (pattern : Twelve) (guard : d1837 pattern = 1) : d19 pattern ≤ (0 : Int) + d1381 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1837, d1381, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c329 pattern childGuard
    simpa only [d1837, d1381, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c331 (pattern : Twelve) (guard : d1837 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1386 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1294, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c330 pattern childGuard
    simpa only [d1294, d1386, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1294, d1386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1294, d1386, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c332 (pattern : Twelve) (guard : d1837 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1393 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1305, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c327 pattern childGuard
    simpa only [d1305, d1393, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1305, d1393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c331 pattern childGuard
    simpa only [d1305, d1393, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c333 (pattern : Twelve) (guard : d1 pattern = 1) : d1279 pattern ≤ (0 : Int) + d1279 pattern := by
  omega
theorem c334 (pattern : Twelve) (guard : d0 pattern = 1) : d1280 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c335 (pattern : Twelve) (guard : d1837 pattern = 1) : d1285 pattern ≤ (0 : Int) + d1382 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1285, d1382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c333 pattern childGuard
    simpa only [d1837, d1285, d1382, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1285, d1382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c334 pattern childGuard
    simpa only [d1837, d1285, d1382, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c336 (pattern : Twelve) (guard : d1837 pattern = 1) : d1295 pattern ≤ (0 : Int) + d1387 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1295, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c252 pattern childGuard
    simpa only [d1295, d1387, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1295, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c335 pattern childGuard
    simpa only [d1295, d1387, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c337 (pattern : Twelve) (guard : d1837 pattern = 1) : d1286 pattern ≤ (0 : Int) + d942 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1286, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d1837, d1286, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1286, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c101 pattern childGuard
    simpa only [d1837, d1286, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c338 (pattern : Twelve) (guard : d1837 pattern = 1) : d1296 pattern ≤ (0 : Int) + d1388 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1296, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c337 pattern childGuard
    simpa only [d1296, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1296, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1296, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c339 (pattern : Twelve) (guard : d1837 pattern = 1) : d1306 pattern ≤ (0 : Int) + d1394 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1306, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c336 pattern childGuard
    simpa only [d1306, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1306, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c338 pattern childGuard
    simpa only [d1306, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c340 (pattern : Twelve) (guard : d1837 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1398 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1313, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c332 pattern childGuard
    simpa only [d1313, d1398, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1313, d1398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c339 pattern childGuard
    simpa only [d1313, d1398, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c341 (pattern : Twelve) (guard : d1837 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1389 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1293, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c260 pattern childGuard
    simpa only [d1293, d1389, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1293, d1389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c326 pattern childGuard
    simpa only [d1293, d1389, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c342 (pattern : Twelve) (guard : d1837 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1395 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1305, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c341 pattern childGuard
    simpa only [d1305, d1395, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1305, d1395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c331 pattern childGuard
    simpa only [d1305, d1395, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c343 (pattern : Twelve) (guard : d1837 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1399 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1313, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c342 pattern childGuard
    simpa only [d1313, d1399, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1313, d1399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c339 pattern childGuard
    simpa only [d1313, d1399, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c344 (pattern : Twelve) (guard : d1837 pattern = 1) : d1313 pattern ≤ (0 : Int) + d1403 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c340 pattern childGuard
    simpa only [d1403, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c343 pattern childGuard
    simpa only [d1403, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c345 (pattern : Twelve) (guard : d0 pattern = 1) : d1281 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c346 (pattern : Twelve) (guard : d1837 pattern = 1) : d1287 pattern ≤ (0 : Int) + d1382 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1287, d1382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c333 pattern childGuard
    simpa only [d1837, d1287, d1382, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1287, d1382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c345 pattern childGuard
    simpa only [d1837, d1287, d1382, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c347 (pattern : Twelve) (guard : d1837 pattern = 1) : d1297 pattern ≤ (0 : Int) + d1387 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1297, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c271 pattern childGuard
    simpa only [d1297, d1387, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1297, d1387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c346 pattern childGuard
    simpa only [d1297, d1387, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c348 (pattern : Twelve) (guard : d0 pattern = 1) : d817 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c349 (pattern : Twelve) (guard : d1837 pattern = 1) : d817 pattern ≤ (0 : Int) + d942 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d1837, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c348 pattern childGuard
    simpa only [d1837, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c350 (pattern : Twelve) (guard : d1837 pattern = 1) : d1298 pattern ≤ (0 : Int) + d1388 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1298, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c349 pattern childGuard
    simpa only [d1298, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1298, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1298, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c351 (pattern : Twelve) (guard : d1837 pattern = 1) : d1307 pattern ≤ (0 : Int) + d1394 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1307, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c347 pattern childGuard
    simpa only [d1307, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1307, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c350 pattern childGuard
    simpa only [d1307, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c352 (pattern : Twelve) (guard : d1 pattern = 1) : d1282 pattern ≤ (0 : Int) + d1282 pattern := by
  omega
theorem c353 (pattern : Twelve) (guard : d0 pattern = 1) : d125 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c354 (pattern : Twelve) (guard : d1837 pattern = 1) : d1288 pattern ≤ (0 : Int) + d1383 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1288, d1383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c352 pattern childGuard
    simpa only [d1837, d1288, d1383, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1288, d1383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c353 pattern childGuard
    simpa only [d1837, d1288, d1383, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c355 (pattern : Twelve) (guard : d1837 pattern = 1) : d1299 pattern ≤ (0 : Int) + d1390 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1299, d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c277 pattern childGuard
    simpa only [d1299, d1390, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1299, d1390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c354 pattern childGuard
    simpa only [d1299, d1390, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c356 (pattern : Twelve) (guard : d1837 pattern = 1) : d1289 pattern ≤ (0 : Int) + d945 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1289, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c278 pattern childGuard
    simpa only [d1837, d1289, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1289, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c144 pattern childGuard
    simpa only [d1837, d1289, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c357 (pattern : Twelve) (guard : d1837 pattern = 1) : d1300 pattern ≤ (0 : Int) + d1391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1300, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d1300, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1300, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1300, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c358 (pattern : Twelve) (guard : d1837 pattern = 1) : d1308 pattern ≤ (0 : Int) + d1396 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1308, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c355 pattern childGuard
    simpa only [d1308, d1396, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1308, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c357 pattern childGuard
    simpa only [d1308, d1396, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c359 (pattern : Twelve) (guard : d1837 pattern = 1) : d1314 pattern ≤ (0 : Int) + d1400 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1314, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c351 pattern childGuard
    simpa only [d1314, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1314, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c358 pattern childGuard
    simpa only [d1314, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c360 (pattern : Twelve) (guard : d1837 pattern = 1) : d1315 pattern ≤ (0 : Int) + d1401 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1315, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c339 pattern childGuard
    simpa only [d1315, d1401, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1315, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1315, d1401, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c361 (pattern : Twelve) (guard : d1837 pattern = 1) : d1319 pattern ≤ (0 : Int) + d1404 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1319, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c359 pattern childGuard
    simpa only [d1319, d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1319, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c360 pattern childGuard
    simpa only [d1319, d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c362 (pattern : Twelve) (guard : d1837 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1405 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1321, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c344 pattern childGuard
    simpa only [d1321, d1405, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1321, d1405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c361 pattern childGuard
    simpa only [d1321, d1405, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c363 (pattern : Twelve) (guard : d1 pattern = 1) : d1283 pattern ≤ (0 : Int) + d1283 pattern := by
  omega
theorem c364 (pattern : Twelve) (guard : d0 pattern = 1) : d1283 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c365 (pattern : Twelve) (guard : d1837 pattern = 1) : d1283 pattern ≤ (0 : Int) + d1384 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c363 pattern childGuard
    simpa only [d1837, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c364 pattern childGuard
    simpa only [d1837, d1384, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c366 (pattern : Twelve) (guard : d1837 pattern = 1) : d1301 pattern ≤ (0 : Int) + d1392 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1301, d1392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c365 pattern childGuard
    simpa only [d1301, d1392, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1301, d1392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1301, d1392, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c367 (pattern : Twelve) (guard : d1837 pattern = 1) : d1309 pattern ≤ (0 : Int) + d1397 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1309, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c341 pattern childGuard
    simpa only [d1309, d1397, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1309, d1397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c366 pattern childGuard
    simpa only [d1309, d1397, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c368 (pattern : Twelve) (guard : d1837 pattern = 1) : d1290 pattern ≤ (0 : Int) + d942 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1290, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d1837, d1290, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1290, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c138 pattern childGuard
    simpa only [d1837, d1290, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c369 (pattern : Twelve) (guard : d1837 pattern = 1) : d1302 pattern ≤ (0 : Int) + d1388 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1302, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c368 pattern childGuard
    simpa only [d1302, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1302, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1302, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c370 (pattern : Twelve) (guard : d1837 pattern = 1) : d1310 pattern ≤ (0 : Int) + d1394 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1310, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c336 pattern childGuard
    simpa only [d1310, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1310, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c369 pattern childGuard
    simpa only [d1310, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c371 (pattern : Twelve) (guard : d1837 pattern = 1) : d1316 pattern ≤ (0 : Int) + d1402 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1316, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c367 pattern childGuard
    simpa only [d1316, d1402, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1316, d1402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c370 pattern childGuard
    simpa only [d1316, d1402, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c372 (pattern : Twelve) (guard : d0 pattern = 1) : d41 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c373 (pattern : Twelve) (guard : d1837 pattern = 1) : d1291 pattern ≤ (0 : Int) + d942 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1291, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c243 pattern childGuard
    simpa only [d1837, d1291, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1291, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c372 pattern childGuard
    simpa only [d1837, d1291, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c374 (pattern : Twelve) (guard : d1837 pattern = 1) : d1303 pattern ≤ (0 : Int) + d1388 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1303, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c373 pattern childGuard
    simpa only [d1303, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1303, d1388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1303, d1388, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c375 (pattern : Twelve) (guard : d1837 pattern = 1) : d1311 pattern ≤ (0 : Int) + d1394 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1311, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c347 pattern childGuard
    simpa only [d1311, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1311, d1394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c374 pattern childGuard
    simpa only [d1311, d1394, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c376 (pattern : Twelve) (guard : d1837 pattern = 1) : d1292 pattern ≤ (0 : Int) + d945 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1292, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c278 pattern childGuard
    simpa only [d1837, d1292, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1292, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c197 pattern childGuard
    simpa only [d1837, d1292, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c377 (pattern : Twelve) (guard : d1837 pattern = 1) : d1304 pattern ≤ (0 : Int) + d1391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1304, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c376 pattern childGuard
    simpa only [d1304, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1304, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1304, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c378 (pattern : Twelve) (guard : d1837 pattern = 1) : d1312 pattern ≤ (0 : Int) + d1396 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1312, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c355 pattern childGuard
    simpa only [d1312, d1396, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1312, d1396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c377 pattern childGuard
    simpa only [d1312, d1396, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c379 (pattern : Twelve) (guard : d1837 pattern = 1) : d1317 pattern ≤ (0 : Int) + d1400 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1317, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c375 pattern childGuard
    simpa only [d1317, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1317, d1400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c378 pattern childGuard
    simpa only [d1317, d1400, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c380 (pattern : Twelve) (guard : d1837 pattern = 1) : d1318 pattern ≤ (0 : Int) + d1401 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1318, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c370 pattern childGuard
    simpa only [d1318, d1401, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1318, d1401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1318, d1401, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c381 (pattern : Twelve) (guard : d1837 pattern = 1) : d1320 pattern ≤ (0 : Int) + d1404 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1320, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c379 pattern childGuard
    simpa only [d1320, d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1320, d1404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c380 pattern childGuard
    simpa only [d1320, d1404, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c382 (pattern : Twelve) (guard : d1837 pattern = 1) : d1322 pattern ≤ (0 : Int) + d1406 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1322, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c371 pattern childGuard
    simpa only [d1322, d1406, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1322, d1406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c381 pattern childGuard
    simpa only [d1322, d1406, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c383 (pattern : Twelve) (guard : d1837 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1408 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1323, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c362 pattern childGuard
    simpa only [d1323, d1408, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1323, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c382 pattern childGuard
    simpa only [d1323, d1408, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c384 (pattern : Twelve) (guard : d1837 pattern = 1) : d1321 pattern ≤ (0 : Int) + d1407 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1321, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c343 pattern childGuard
    simpa only [d1321, d1407, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1321, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c361 pattern childGuard
    simpa only [d1321, d1407, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c385 (pattern : Twelve) (guard : d1837 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1409 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1323, d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c384 pattern childGuard
    simpa only [d1323, d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1323, d1409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c382 pattern childGuard
    simpa only [d1323, d1409, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c386 (pattern : Twelve) (guard : d1837 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1410 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c383 pattern childGuard
    simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c385 pattern childGuard
    simpa only [d1410, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c387 (pattern : Twelve) (guard : d1837 pattern = 1) : d1323 pattern ≤ (0 : Int) + d1411 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c386 pattern childGuard
    simpa only [d1411, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c385 pattern childGuard
    simpa only [d1411, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c388 (pattern : Twelve) (guard : d1 pattern = 1) : d1324 pattern ≤ (0 : Int) + d1324 pattern := by
  omega
theorem c389 (pattern : Twelve) (guard : d0 pattern = 1) : d1324 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c390 (pattern : Twelve) (guard : d1837 pattern = 1) : d1324 pattern ≤ (0 : Int) + d1689 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c388 pattern childGuard
    simpa only [d1837, d1689, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c389 pattern childGuard
    simpa only [d1837, d1689, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c391 (pattern : Twelve) (guard : d1837 pattern = 1) : d1649 pattern ≤ (0 : Int) + d1693 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1649, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c330 pattern childGuard
    simpa only [d1649, d1693, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1649, d1693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c390 pattern childGuard
    simpa only [d1649, d1693, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c392 (pattern : Twelve) (guard : d1 pattern = 1) : d25 pattern ≤ (0 : Int) + d25 pattern := by
  omega
theorem c393 (pattern : Twelve) (guard : d0 pattern = 1) : d25 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c394 (pattern : Twelve) (guard : d1837 pattern = 1) : d25 pattern ≤ (0 : Int) + d1690 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c392 pattern childGuard
    simpa only [d1837, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c393 pattern childGuard
    simpa only [d1837, d1690, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c395 (pattern : Twelve) (guard : d1837 pattern = 1) : d1650 pattern ≤ (0 : Int) + d1694 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1650, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c394 pattern childGuard
    simpa only [d1650, d1694, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1650, d1694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1650, d1694, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c396 (pattern : Twelve) (guard : d1837 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1697 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1656, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c391 pattern childGuard
    simpa only [d1656, d1697, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1656, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c395 pattern childGuard
    simpa only [d1656, d1697, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c397 (pattern : Twelve) (guard : d1 pattern = 1) : d1644 pattern ≤ (0 : Int) + d1644 pattern := by
  omega
theorem c398 (pattern : Twelve) (guard : d0 pattern = 1) : d1645 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c399 (pattern : Twelve) (guard : d1837 pattern = 1) : d1647 pattern ≤ (0 : Int) + d1691 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1647, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c397 pattern childGuard
    simpa only [d1837, d1647, d1691, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1647, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d1837, d1647, d1691, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c400 (pattern : Twelve) (guard : d1837 pattern = 1) : d1651 pattern ≤ (0 : Int) + d1695 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1651, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c337 pattern childGuard
    simpa only [d1651, d1695, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1651, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c399 pattern childGuard
    simpa only [d1651, d1695, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c401 (pattern : Twelve) (guard : d1837 pattern = 1) : d1657 pattern ≤ (0 : Int) + d1698 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1657, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c400 pattern childGuard
    simpa only [d1657, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1657, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c357 pattern childGuard
    simpa only [d1657, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c402 (pattern : Twelve) (guard : d1837 pattern = 1) : d1660 pattern ≤ (0 : Int) + d1700 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1660, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c396 pattern childGuard
    simpa only [d1660, d1700, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1660, d1700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c401 pattern childGuard
    simpa only [d1660, d1700, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c403 (pattern : Twelve) (guard : d0 pattern = 1) : d1644 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c404 (pattern : Twelve) (guard : d1837 pattern = 1) : d1644 pattern ≤ (0 : Int) + d1691 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c397 pattern childGuard
    simpa only [d1837, d1691, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c403 pattern childGuard
    simpa only [d1837, d1691, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c405 (pattern : Twelve) (guard : d1837 pattern = 1) : d1652 pattern ≤ (0 : Int) + d1695 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1652, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c349 pattern childGuard
    simpa only [d1652, d1695, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1652, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c404 pattern childGuard
    simpa only [d1652, d1695, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c406 (pattern : Twelve) (guard : d0 pattern = 1) : d821 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c407 (pattern : Twelve) (guard : d1837 pattern = 1) : d821 pattern ≤ (0 : Int) + d945 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c278 pattern childGuard
    simpa only [d1837, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c406 pattern childGuard
    simpa only [d1837, d945, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c408 (pattern : Twelve) (guard : d1837 pattern = 1) : d1653 pattern ≤ (0 : Int) + d1391 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1653, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c407 pattern childGuard
    simpa only [d1653, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1653, d1391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1653, d1391, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c409 (pattern : Twelve) (guard : d1837 pattern = 1) : d1658 pattern ≤ (0 : Int) + d1698 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1658, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c405 pattern childGuard
    simpa only [d1658, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1658, d1698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c408 pattern childGuard
    simpa only [d1658, d1698, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c410 (pattern : Twelve) (guard : d1 pattern = 1) : d1646 pattern ≤ (0 : Int) + d1646 pattern := by
  omega
theorem c411 (pattern : Twelve) (guard : d0 pattern = 1) : d128 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c412 (pattern : Twelve) (guard : d1837 pattern = 1) : d1648 pattern ≤ (0 : Int) + d1692 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1648, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c410 pattern childGuard
    simpa only [d1837, d1648, d1692, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1648, d1692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c411 pattern childGuard
    simpa only [d1837, d1648, d1692, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c413 (pattern : Twelve) (guard : d1837 pattern = 1) : d1654 pattern ≤ (0 : Int) + d1696 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1654, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c356 pattern childGuard
    simpa only [d1654, d1696, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1654, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c412 pattern childGuard
    simpa only [d1654, d1696, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c414 (pattern : Twelve) (guard : d1 pattern = 1) : d822 pattern ≤ (0 : Int) + d822 pattern := by
  omega
theorem c415 (pattern : Twelve) (guard : d1837 pattern = 1) : d822 pattern ≤ (0 : Int) + d1252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1837, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c414 pattern childGuard
    simpa only [d1837, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1837, d1252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c279 pattern childGuard
    simpa only [d1837, d1252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c416 (pattern : Twelve) (guard : d1837 pattern = 1) : d1655 pattern ≤ (0 : Int) + d1626 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c415 pattern childGuard
    simpa only [d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1655, d1626, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c417 (pattern : Twelve) (guard : d1837 pattern = 1) : d1659 pattern ≤ (0 : Int) + d1699 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1659, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c413 pattern childGuard
    simpa only [d1659, d1699, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1659, d1699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c416 pattern childGuard
    simpa only [d1659, d1699, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c418 (pattern : Twelve) (guard : d1837 pattern = 1) : d1661 pattern ≤ (0 : Int) + d1701 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1661, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c409 pattern childGuard
    simpa only [d1661, d1701, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1661, d1701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c417 pattern childGuard
    simpa only [d1661, d1701, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c419 (pattern : Twelve) (guard : d1837 pattern = 1) : d1662 pattern ≤ (0 : Int) + d1702 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1662, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c401 pattern childGuard
    simpa only [d1662, d1702, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1837 pattern = 1 := by simpa only [d1662, d1702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c153 pattern childGuard
    simpa only [d1662, d1702, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
