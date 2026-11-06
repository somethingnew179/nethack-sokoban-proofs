/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons029
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c4200 (pattern : Twelve) (guard : d1869 pattern = 1) : d360 pattern ≤ (0 : Int) + d407 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4198 pattern childGuard
    simpa only [d360, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4199 pattern childGuard
    simpa only [d360, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4201 (pattern : Twelve) (guard : d1869 pattern = 1) : d357 pattern ≤ (0 : Int) + d413 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d357, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4197 pattern childGuard
    simpa only [d1869, d357, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d357, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4190 pattern childGuard
    simpa only [d1869, d357, d413, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4202 (pattern : Twelve) (guard : d1869 pattern = 1) : d360 pattern ≤ (0 : Int) + d417 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d360, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4201 pattern childGuard
    simpa only [d360, d417, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d360, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4183 pattern childGuard
    simpa only [d360, d417, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4203 (pattern : Twelve) (guard : d1869 pattern = 1) : d360 pattern ≤ (0 : Int) + d420 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4200 pattern childGuard
    simpa only [d420, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4202 pattern childGuard
    simpa only [d420, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4204 (pattern : Twelve) (guard : d1869 pattern = 1) : d363 pattern ≤ (0 : Int) + d420 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4203 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4194 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4205 (pattern : Twelve) (guard : d1869 pattern = 1) : d364 pattern ≤ (0 : Int) + d423 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d364, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4195 pattern childGuard
    simpa only [d364, d423, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d364, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4204 pattern childGuard
    simpa only [d364, d423, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4206 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d408 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4207 (pattern : Twelve) (guard : d1869 pattern = 1) : d357 pattern ≤ (0 : Int) + d414 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d357, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4197 pattern childGuard
    simpa only [d1869, d357, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d357, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4206 pattern childGuard
    simpa only [d1869, d357, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4208 (pattern : Twelve) (guard : d1869 pattern = 1) : d360 pattern ≤ (0 : Int) + d418 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d360, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4207 pattern childGuard
    simpa only [d360, d418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d360, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4183 pattern childGuard
    simpa only [d360, d418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4209 (pattern : Twelve) (guard : d1869 pattern = 1) : d360 pattern ≤ (0 : Int) + d421 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4200 pattern childGuard
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4208 pattern childGuard
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4210 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d414 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d356, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4187 pattern childGuard
    simpa only [d1869, d356, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d356, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4206 pattern childGuard
    simpa only [d1869, d356, d414, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4211 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d418 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4210 pattern childGuard
    simpa only [d418, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4192 pattern childGuard
    simpa only [d418, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4212 (pattern : Twelve) (guard : d1869 pattern = 1) : d356 pattern ≤ (0 : Int) + d421 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4189 pattern childGuard
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4211 pattern childGuard
    simpa only [d421, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4213 (pattern : Twelve) (guard : d1869 pattern = 1) : d363 pattern ≤ (0 : Int) + d421 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4209 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4212 pattern childGuard
    simpa only [d363, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4214 (pattern : Twelve) (guard : d1869 pattern = 1) : d365 pattern ≤ (0 : Int) + d424 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d365, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4205 pattern childGuard
    simpa only [d365, d424, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d365, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4213 pattern childGuard
    simpa only [d365, d424, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4215 (pattern : Twelve) (guard : d1 pattern = 1) : d814 pattern ≤ (0 : Int) + d814 pattern := by
  omega
theorem c4216 (pattern : Twelve) (guard : d1848 pattern = 1) : d816 pattern ≤ (0 : Int) + d818 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d816, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4215 pattern childGuard
    simpa only [d1848, d816, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d816, d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1356 pattern childGuard
    simpa only [d1848, d816, d818, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4217 (pattern : Twelve) (guard : d1848 pattern = 1) : d824 pattern ≤ (0 : Int) + d1030 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d824, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1397 pattern childGuard
    simpa only [d824, d1030, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d824, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4216 pattern childGuard
    simpa only [d824, d1030, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4218 (pattern : Twelve) (guard : d1848 pattern = 1) : d838 pattern ≤ (0 : Int) + d1038 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2664 pattern childGuard
    simpa only [d838, d1038, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4217 pattern childGuard
    simpa only [d838, d1038, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4219 (pattern : Twelve) (guard : d1848 pattern = 1) : d825 pattern ≤ (0 : Int) + d1032 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d825, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1405 pattern childGuard
    simpa only [d825, d1032, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d825, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2806 pattern childGuard
    simpa only [d825, d1032, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4220 (pattern : Twelve) (guard : d1848 pattern = 1) : d839 pattern ≤ (0 : Int) + d1039 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2746 pattern childGuard
    simpa only [d839, d1039, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4219 pattern childGuard
    simpa only [d839, d1039, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4221 (pattern : Twelve) (guard : d1848 pattern = 1) : d853 pattern ≤ (0 : Int) + d1048 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4218 pattern childGuard
    simpa only [d853, d1048, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d1048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4220 pattern childGuard
    simpa only [d853, d1048, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4222 (pattern : Twelve) (guard : d0 pattern = 1) : d913 pattern ≤ (0 : Int) + d1049 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4223 (pattern : Twelve) (guard : d1869 pattern = 1) : d1018 pattern ≤ (0 : Int) + d1054 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1018, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4221 pattern childGuard
    simpa only [d1869, d1018, d1054, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1018, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4222 pattern childGuard
    simpa only [d1869, d1018, d1054, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4224 (pattern : Twelve) (guard : d1848 pattern = 1) : d824 pattern ≤ (0 : Int) + d1033 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d824, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1415 pattern childGuard
    simpa only [d824, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d824, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4216 pattern childGuard
    simpa only [d824, d1033, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4225 (pattern : Twelve) (guard : d1848 pattern = 1) : d838 pattern ≤ (0 : Int) + d1040 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2677 pattern childGuard
    simpa only [d838, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4224 pattern childGuard
    simpa only [d838, d1040, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4226 (pattern : Twelve) (guard : d1848 pattern = 1) : d839 pattern ≤ (0 : Int) + d1041 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1418 pattern childGuard
    simpa only [d839, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d839, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4219 pattern childGuard
    simpa only [d839, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4227 (pattern : Twelve) (guard : d1848 pattern = 1) : d853 pattern ≤ (0 : Int) + d1049 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4225 pattern childGuard
    simpa only [d853, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d1049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4226 pattern childGuard
    simpa only [d853, d1049, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4228 (pattern : Twelve) (guard : d0 pattern = 1) : d914 pattern ≤ (0 : Int) + d1050 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4229 (pattern : Twelve) (guard : d1869 pattern = 1) : d1019 pattern ≤ (0 : Int) + d1055 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1019, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4227 pattern childGuard
    simpa only [d1869, d1019, d1055, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1019, d1055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4228 pattern childGuard
    simpa only [d1869, d1019, d1055, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4230 (pattern : Twelve) (guard : d1869 pattern = 1) : d1023 pattern ≤ (0 : Int) + d1060 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1023, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4223 pattern childGuard
    simpa only [d1023, d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1023, d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4229 pattern childGuard
    simpa only [d1023, d1060, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4231 (pattern : Twelve) (guard : d1848 pattern = 1) : d838 pattern ≤ (0 : Int) + d1043 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4173 pattern childGuard
    simpa only [d838, d1043, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d1043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4224 pattern childGuard
    simpa only [d838, d1043, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4232 (pattern : Twelve) (guard : d1848 pattern = 1) : d853 pattern ≤ (0 : Int) + d1051 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4231 pattern childGuard
    simpa only [d853, d1051, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d1051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4226 pattern childGuard
    simpa only [d853, d1051, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4233 (pattern : Twelve) (guard : d0 pattern = 1) : d916 pattern ≤ (0 : Int) + d1052 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4234 (pattern : Twelve) (guard : d1869 pattern = 1) : d1020 pattern ≤ (0 : Int) + d1056 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1020, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4232 pattern childGuard
    simpa only [d1869, d1020, d1056, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1020, d1056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4233 pattern childGuard
    simpa only [d1869, d1020, d1056, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4235 (pattern : Twelve) (guard : d1848 pattern = 1) : d838 pattern ≤ (0 : Int) + d1042 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1354 pattern childGuard
    simpa only [d838, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d838, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4224 pattern childGuard
    simpa only [d838, d1042, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4236 (pattern : Twelve) (guard : d1848 pattern = 1) : d853 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4235 pattern childGuard
    simpa only [d853, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d853, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4226 pattern childGuard
    simpa only [d853, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4237 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d1057 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1021, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4236 pattern childGuard
    simpa only [d1869, d1021, d1057, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1021, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1021, d1057, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4238 (pattern : Twelve) (guard : d1869 pattern = 1) : d1024 pattern ≤ (0 : Int) + d1061 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1024, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4234 pattern childGuard
    simpa only [d1024, d1061, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1024, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4237 pattern childGuard
    simpa only [d1024, d1061, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4239 (pattern : Twelve) (guard : d1869 pattern = 1) : d1025 pattern ≤ (0 : Int) + d1064 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1025, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4230 pattern childGuard
    simpa only [d1025, d1064, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1025, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4238 pattern childGuard
    simpa only [d1025, d1064, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4240 (pattern : Twelve) (guard : d1848 pattern = 1) : d846 pattern ≤ (0 : Int) + d1041 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d846, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1441 pattern childGuard
    simpa only [d846, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d846, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4219 pattern childGuard
    simpa only [d846, d1041, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4241 (pattern : Twelve) (guard : d1848 pattern = 1) : d857 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d857, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4235 pattern childGuard
    simpa only [d857, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d857, d1050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4240 pattern childGuard
    simpa only [d857, d1050, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4242 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1050 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4243 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4241 pattern childGuard
    simpa only [d1869, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4242 pattern childGuard
    simpa only [d1869, d1022, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4244 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1052 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4245 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d1058 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1022, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4241 pattern childGuard
    simpa only [d1869, d1022, d1058, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1022, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4244 pattern childGuard
    simpa only [d1869, d1022, d1058, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4246 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d1057 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1022, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4241 pattern childGuard
    simpa only [d1869, d1022, d1057, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1022, d1057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1022, d1057, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4247 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d1062 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4245 pattern childGuard
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4246 pattern childGuard
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4248 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d1065 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4243 pattern childGuard
    simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4247 pattern childGuard
    simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4249 (pattern : Twelve) (guard : d1869 pattern = 1) : d1026 pattern ≤ (0 : Int) + d1067 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1026, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4239 pattern childGuard
    simpa only [d1026, d1067, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1026, d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4248 pattern childGuard
    simpa only [d1026, d1067, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4250 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d1050 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4236 pattern childGuard
    simpa only [d1869, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4242 pattern childGuard
    simpa only [d1869, d1021, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4251 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d1058 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1021, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4236 pattern childGuard
    simpa only [d1869, d1021, d1058, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1021, d1058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4244 pattern childGuard
    simpa only [d1869, d1021, d1058, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4252 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d1062 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4251 pattern childGuard
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4237 pattern childGuard
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4253 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d1065 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4250 pattern childGuard
    simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4252 pattern childGuard
    simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4254 (pattern : Twelve) (guard : d1869 pattern = 1) : d1027 pattern ≤ (0 : Int) + d1065 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4253 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4248 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4255 (pattern : Twelve) (guard : d1869 pattern = 1) : d1028 pattern ≤ (0 : Int) + d1068 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1028, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4249 pattern childGuard
    simpa only [d1028, d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1028, d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4254 pattern childGuard
    simpa only [d1028, d1068, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4256 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1053 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4257 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d1059 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1021, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4236 pattern childGuard
    simpa only [d1869, d1021, d1059, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1021, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4256 pattern childGuard
    simpa only [d1869, d1021, d1059, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4258 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d1063 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4257 pattern childGuard
    simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4237 pattern childGuard
    simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4259 (pattern : Twelve) (guard : d1869 pattern = 1) : d1021 pattern ≤ (0 : Int) + d1066 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4250 pattern childGuard
    simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4258 pattern childGuard
    simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4260 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d1059 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1022, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4241 pattern childGuard
    simpa only [d1869, d1022, d1059, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1022, d1059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4256 pattern childGuard
    simpa only [d1869, d1022, d1059, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4261 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d1063 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4260 pattern childGuard
    simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4246 pattern childGuard
    simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4262 (pattern : Twelve) (guard : d1869 pattern = 1) : d1022 pattern ≤ (0 : Int) + d1066 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4243 pattern childGuard
    simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4261 pattern childGuard
    simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4263 (pattern : Twelve) (guard : d1869 pattern = 1) : d1027 pattern ≤ (0 : Int) + d1066 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4259 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4262 pattern childGuard
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4264 (pattern : Twelve) (guard : d1869 pattern = 1) : d1029 pattern ≤ (0 : Int) + d1069 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1029, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4255 pattern childGuard
    simpa only [d1029, d1069, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1029, d1069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4263 pattern childGuard
    simpa only [d1029, d1069, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4265 (pattern : Twelve) (guard : d1 pattern = 1) : d872 pattern ≤ (0 : Int) + d872 pattern := by
  omega
theorem c4266 (pattern : Twelve) (guard : d1848 pattern = 1) : d872 pattern ≤ (0 : Int) + d1280 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4265 pattern childGuard
    simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c325 pattern childGuard
    simpa only [d1848, d1280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4267 (pattern : Twelve) (guard : d1848 pattern = 1) : d1284 pattern ≤ (0 : Int) + d1445 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1284, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1470 pattern childGuard
    simpa only [d1284, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1284, d1445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4266 pattern childGuard
    simpa only [d1284, d1445, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4268 (pattern : Twelve) (guard : d1848 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1448 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1293, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2746 pattern childGuard
    simpa only [d1293, d1448, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1293, d1448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4267 pattern childGuard
    simpa only [d1293, d1448, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4269 (pattern : Twelve) (guard : d1848 pattern = 1) : d6 pattern ≤ (0 : Int) + d6 pattern := by
  omega
theorem c4270 (pattern : Twelve) (guard : d1848 pattern = 1) : d1294 pattern ≤ (0 : Int) + d1449 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1294, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1473 pattern childGuard
    simpa only [d1294, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1294, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1294, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4271 (pattern : Twelve) (guard : d1848 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1455 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4268 pattern childGuard
    simpa only [d1305, d1455, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4270 pattern childGuard
    simpa only [d1305, d1455, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4272 (pattern : Twelve) (guard : d0 pattern = 1) : d1357 pattern ≤ (0 : Int) + d1456 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4273 (pattern : Twelve) (guard : d1869 pattern = 1) : d1435 pattern ≤ (0 : Int) + d1459 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1435, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4271 pattern childGuard
    simpa only [d1869, d1435, d1459, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1435, d1459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4272 pattern childGuard
    simpa only [d1869, d1435, d1459, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4274 (pattern : Twelve) (guard : d1848 pattern = 1) : d1293 pattern ≤ (0 : Int) + d1450 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1293, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1418 pattern childGuard
    simpa only [d1293, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1293, d1450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4267 pattern childGuard
    simpa only [d1293, d1450, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4275 (pattern : Twelve) (guard : d1848 pattern = 1) : d1305 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4274 pattern childGuard
    simpa only [d1305, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1305, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4270 pattern childGuard
    simpa only [d1305, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4276 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1456 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4277 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4275 pattern childGuard
    simpa only [d1869, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4276 pattern childGuard
    simpa only [d1869, d1436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4278 (pattern : Twelve) (guard : d1869 pattern = 1) : d1438 pattern ≤ (0 : Int) + d1463 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1438, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4273 pattern childGuard
    simpa only [d1438, d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1438, d1463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4277 pattern childGuard
    simpa only [d1438, d1463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4279 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1457 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4280 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1460 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1436, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4275 pattern childGuard
    simpa only [d1869, d1436, d1460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1436, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4279 pattern childGuard
    simpa only [d1869, d1436, d1460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4281 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1461 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1436, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4275 pattern childGuard
    simpa only [d1869, d1436, d1461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1436, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1436, d1461, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4282 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1464 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4280 pattern childGuard
    simpa only [d1464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4281 pattern childGuard
    simpa only [d1464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4283 (pattern : Twelve) (guard : d1869 pattern = 1) : d1439 pattern ≤ (0 : Int) + d1466 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1439, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4278 pattern childGuard
    simpa only [d1439, d1466, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1439, d1466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4282 pattern childGuard
    simpa only [d1439, d1466, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4284 (pattern : Twelve) (guard : d1848 pattern = 1) : d1301 pattern ≤ (0 : Int) + d1449 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1301, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1501 pattern childGuard
    simpa only [d1301, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1301, d1449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1301, d1449, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4285 (pattern : Twelve) (guard : d1848 pattern = 1) : d1309 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1309, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4274 pattern childGuard
    simpa only [d1309, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1309, d1456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4284 pattern childGuard
    simpa only [d1309, d1456, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4286 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1456 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4285 pattern childGuard
    simpa only [d1869, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4276 pattern childGuard
    simpa only [d1869, d1437, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4287 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1460 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1437, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4285 pattern childGuard
    simpa only [d1869, d1437, d1460, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1437, d1460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4279 pattern childGuard
    simpa only [d1869, d1437, d1460, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4288 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1461 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1437, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4285 pattern childGuard
    simpa only [d1869, d1437, d1461, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1437, d1461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1437, d1461, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4289 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1464 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4287 pattern childGuard
    simpa only [d1464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4288 pattern childGuard
    simpa only [d1464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4290 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1467 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4286 pattern childGuard
    simpa only [d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4289 pattern childGuard
    simpa only [d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4291 (pattern : Twelve) (guard : d1869 pattern = 1) : d1440 pattern ≤ (0 : Int) + d1469 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1440, d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4283 pattern childGuard
    simpa only [d1440, d1469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1440, d1469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4290 pattern childGuard
    simpa only [d1440, d1469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4292 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1467 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4277 pattern childGuard
    simpa only [d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4282 pattern childGuard
    simpa only [d1467, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4293 (pattern : Twelve) (guard : d1869 pattern = 1) : d1441 pattern ≤ (0 : Int) + d1467 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4292 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4290 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4294 (pattern : Twelve) (guard : d1869 pattern = 1) : d1442 pattern ≤ (0 : Int) + d1470 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1442, d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4291 pattern childGuard
    simpa only [d1442, d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1442, d1470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4293 pattern childGuard
    simpa only [d1442, d1470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4295 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1458 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4296 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1462 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1436, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4275 pattern childGuard
    simpa only [d1869, d1436, d1462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1436, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4295 pattern childGuard
    simpa only [d1869, d1436, d1462, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4297 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1465 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4296 pattern childGuard
    simpa only [d1465, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4281 pattern childGuard
    simpa only [d1465, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4298 (pattern : Twelve) (guard : d1869 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1468 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4277 pattern childGuard
    simpa only [d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4297 pattern childGuard
    simpa only [d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4299 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1462 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1437, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4285 pattern childGuard
    simpa only [d1869, d1437, d1462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1437, d1462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4295 pattern childGuard
    simpa only [d1869, d1437, d1462, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4300 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1465 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4299 pattern childGuard
    simpa only [d1465, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4288 pattern childGuard
    simpa only [d1465, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4301 (pattern : Twelve) (guard : d1869 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1468 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4286 pattern childGuard
    simpa only [d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4300 pattern childGuard
    simpa only [d1468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4302 (pattern : Twelve) (guard : d1869 pattern = 1) : d1441 pattern ≤ (0 : Int) + d1468 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4298 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4301 pattern childGuard
    simpa only [d1441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4303 (pattern : Twelve) (guard : d1869 pattern = 1) : d1443 pattern ≤ (0 : Int) + d1471 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1443, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4294 pattern childGuard
    simpa only [d1443, d1471, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1443, d1471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4302 pattern childGuard
    simpa only [d1443, d1471, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4304 (pattern : Twelve) (guard : d1848 pattern = 1) : d1649 pattern ≤ (0 : Int) + d1716 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1649, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1473 pattern childGuard
    simpa only [d1649, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1649, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1523 pattern childGuard
    simpa only [d1649, d1716, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4305 (pattern : Twelve) (guard : d1848 pattern = 1) : d1650 pattern ≤ (0 : Int) + d1452 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1650, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1526 pattern childGuard
    simpa only [d1650, d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1650, d1452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4269 pattern childGuard
    simpa only [d1650, d1452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4306 (pattern : Twelve) (guard : d1848 pattern = 1) : d1656 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1656, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4304 pattern childGuard
    simpa only [d1656, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1656, d1719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4305 pattern childGuard
    simpa only [d1656, d1719, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4307 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1719 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4308 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1719 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4306 pattern childGuard
    simpa only [d1869, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4307 pattern childGuard
    simpa only [d1869, d1715, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4309 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1720 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4310 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1722 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1715, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4306 pattern childGuard
    simpa only [d1869, d1715, d1722, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1715, d1722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4309 pattern childGuard
    simpa only [d1869, d1715, d1722, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4311 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1723 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1715, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4306 pattern childGuard
    simpa only [d1869, d1715, d1723, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1715, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1869, d1715, d1723, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4312 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1725 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4310 pattern childGuard
    simpa only [d1725, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4311 pattern childGuard
    simpa only [d1725, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4313 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1727 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4308 pattern childGuard
    simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4312 pattern childGuard
    simpa only [d1727, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4314 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1721 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4315 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1724 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1869, d1715, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4306 pattern childGuard
    simpa only [d1869, d1715, d1724, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1869, d1715, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4314 pattern childGuard
    simpa only [d1869, d1715, d1724, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4316 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1726 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4315 pattern childGuard
    simpa only [d1726, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4311 pattern childGuard
    simpa only [d1726, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4317 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1728 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4308 pattern childGuard
    simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4316 pattern childGuard
    simpa only [d1728, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4318 (pattern : Twelve) (guard : d1869 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1729 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4313 pattern childGuard
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1869 pattern = 1 := by simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4317 pattern childGuard
    simpa only [d1729, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4319 (pattern : Twelve) (guard : d0 pattern = 1) : d208 pattern ≤ (0 : Int) + d92 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4320 (pattern : Twelve) (guard : d1844 pattern = 1) : d352 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d352, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c732 pattern childGuard
    simpa only [d1844, d352, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d352, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4319 pattern childGuard
    simpa only [d1844, d352, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4321 (pattern : Twelve) (guard : d0 pattern = 1) : d209 pattern ≤ (0 : Int) + d94 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4322 (pattern : Twelve) (guard : d1844 pattern = 1) : d353 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d353, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4077 pattern childGuard
    simpa only [d1844, d353, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d353, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4321 pattern childGuard
    simpa only [d1844, d353, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4323 (pattern : Twelve) (guard : d1844 pattern = 1) : d358 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d358, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4320 pattern childGuard
    simpa only [d358, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d358, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4322 pattern childGuard
    simpa only [d358, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4324 (pattern : Twelve) (guard : d0 pattern = 1) : d359 pattern ≤ (0 : Int) + d217 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4325 (pattern : Twelve) (guard : d1868 pattern = 1) : d361 pattern ≤ (0 : Int) + d345 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d361, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4323 pattern childGuard
    simpa only [d1868, d361, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d361, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4324 pattern childGuard
    simpa only [d1868, d361, d345, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4326 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d98 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4327 (pattern : Twelve) (guard : d1844 pattern = 1) : d356 pattern ≤ (0 : Int) + d106 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d356, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c739 pattern childGuard
    simpa only [d1844, d356, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d356, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4326 pattern childGuard
    simpa only [d1844, d356, d106, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4328 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d99 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4329 (pattern : Twelve) (guard : d1844 pattern = 1) : d356 pattern ≤ (0 : Int) + d107 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d356, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c739 pattern childGuard
    simpa only [d1844, d356, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d356, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4328 pattern childGuard
    simpa only [d1844, d356, d107, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4330 (pattern : Twelve) (guard : d1844 pattern = 1) : d356 pattern ≤ (0 : Int) + d112 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4327 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4329 pattern childGuard
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4331 (pattern : Twelve) (guard : d0 pattern = 1) : d356 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4332 (pattern : Twelve) (guard : d1868 pattern = 1) : d356 pattern ≤ (0 : Int) + d346 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4330 pattern childGuard
    simpa only [d1868, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4331 pattern childGuard
    simpa only [d1868, d346, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4333 (pattern : Twelve) (guard : d1868 pattern = 1) : d362 pattern ≤ (0 : Int) + d348 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d362, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4325 pattern childGuard
    simpa only [d362, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d362, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d362, d348, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4334 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d92 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4335 (pattern : Twelve) (guard : d1844 pattern = 1) : d357 pattern ≤ (0 : Int) + d102 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d357, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c732 pattern childGuard
    simpa only [d1844, d357, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d357, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4334 pattern childGuard
    simpa only [d1844, d357, d102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4336 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d94 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4337 (pattern : Twelve) (guard : d1844 pattern = 1) : d355 pattern ≤ (0 : Int) + d103 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d355, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4077 pattern childGuard
    simpa only [d1844, d355, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d355, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4336 pattern childGuard
    simpa only [d1844, d355, d103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4338 (pattern : Twelve) (guard : d1844 pattern = 1) : d360 pattern ≤ (0 : Int) + d110 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d360, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4335 pattern childGuard
    simpa only [d360, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d360, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4337 pattern childGuard
    simpa only [d360, d110, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4339 (pattern : Twelve) (guard : d0 pattern = 1) : d360 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban21.Diagram
