/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons037
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c5320 (pattern : Twelve) (guard : d1870 pattern = 1) : d412 pattern ≤ (0 : Int) + d462 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d412, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5310 pattern childGuard
    simpa only [d412, d462, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d412, d462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5294 pattern childGuard
    simpa only [d412, d462, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5321 (pattern : Twelve) (guard : d1870 pattern = 1) : d417 pattern ≤ (0 : Int) + d468 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d417, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5319 pattern childGuard
    simpa only [d417, d468, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d417, d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5320 pattern childGuard
    simpa only [d417, d468, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5322 (pattern : Twelve) (guard : d1870 pattern = 1) : d420 pattern ≤ (0 : Int) + d472 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d420, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5312 pattern childGuard
    simpa only [d420, d472, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d420, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5321 pattern childGuard
    simpa only [d420, d472, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5323 (pattern : Twelve) (guard : d1870 pattern = 1) : d422 pattern ≤ (0 : Int) + d474 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d422, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5297 pattern childGuard
    simpa only [d422, d474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d422, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5322 pattern childGuard
    simpa only [d422, d474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5324 (pattern : Twelve) (guard : d1870 pattern = 1) : d423 pattern ≤ (0 : Int) + d475 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d423, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5323 pattern childGuard
    simpa only [d423, d475, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d423, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5322 pattern childGuard
    simpa only [d423, d475, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5325 (pattern : Twelve) (guard : d1870 pattern = 1) : d407 pattern ≤ (0 : Int) + d452 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5304 pattern childGuard
    simpa only [d407, d452, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, d452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5273 pattern childGuard
    simpa only [d407, d452, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5326 (pattern : Twelve) (guard : d1870 pattern = 1) : d407 pattern ≤ (0 : Int) + d463 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5301 pattern childGuard
    simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5325 pattern childGuard
    simpa only [d463, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5327 (pattern : Twelve) (guard : d1870 pattern = 1) : d407 pattern ≤ (0 : Int) + d469 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5326 pattern childGuard
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5311 pattern childGuard
    simpa only [d469, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5328 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d3 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5329 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (0 : Int) + d123 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d35, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d35, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d35, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5328 pattern childGuard
    simpa only [d1848, d35, d123, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5330 (pattern : Twelve) (guard : d1848 pattern = 1) : d35 pattern ≤ (0 : Int) + d132 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5329 pattern childGuard
    simpa only [d132, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5331 (pattern : Twelve) (guard : d1870 pattern = 1) : d394 pattern ≤ (0 : Int) + d442 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d394, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5330 pattern childGuard
    simpa only [d1870, d394, d442, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d394, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5272 pattern childGuard
    simpa only [d1870, d394, d442, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5332 (pattern : Twelve) (guard : d1870 pattern = 1) : d407 pattern ≤ (0 : Int) + d453 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5313 pattern childGuard
    simpa only [d407, d453, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d407, d453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5331 pattern childGuard
    simpa only [d407, d453, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5333 (pattern : Twelve) (guard : d0 pattern = 1) : d386 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5334 (pattern : Twelve) (guard : d1870 pattern = 1) : d400 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d400, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d1870, d400, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d400, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5333 pattern childGuard
    simpa only [d1870, d400, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5335 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d5 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5336 (pattern : Twelve) (guard : d1848 pattern = 1) : d39 pattern ≤ (0 : Int) + d126 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d39, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1333 pattern childGuard
    simpa only [d1848, d39, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d39, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5335 pattern childGuard
    simpa only [d1848, d39, d126, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5337 (pattern : Twelve) (guard : d1848 pattern = 1) : d47 pattern ≤ (0 : Int) + d47 pattern := by
  omega
theorem c5338 (pattern : Twelve) (guard : d1848 pattern = 1) : d387 pattern ≤ (0 : Int) + d134 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d387, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5336 pattern childGuard
    simpa only [d387, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d387, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5337 pattern childGuard
    simpa only [d387, d134, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5339 (pattern : Twelve) (guard : d0 pattern = 1) : d388 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5340 (pattern : Twelve) (guard : d1870 pattern = 1) : d401 pattern ≤ (0 : Int) + d443 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d401, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5338 pattern childGuard
    simpa only [d1870, d401, d443, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d401, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5339 pattern childGuard
    simpa only [d1870, d401, d443, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5341 (pattern : Twelve) (guard : d1870 pattern = 1) : d408 pattern ≤ (0 : Int) + d454 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d408, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5334 pattern childGuard
    simpa only [d408, d454, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d408, d454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5340 pattern childGuard
    simpa only [d408, d454, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5342 (pattern : Twelve) (guard : d1870 pattern = 1) : d414 pattern ≤ (0 : Int) + d464 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d414, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5332 pattern childGuard
    simpa only [d414, d464, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d414, d464, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5341 pattern childGuard
    simpa only [d414, d464, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5343 (pattern : Twelve) (guard : d1870 pattern = 1) : d418 pattern ≤ (0 : Int) + d470 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d418, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5342 pattern childGuard
    simpa only [d418, d470, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d418, d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5320 pattern childGuard
    simpa only [d418, d470, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5344 (pattern : Twelve) (guard : d1870 pattern = 1) : d421 pattern ≤ (0 : Int) + d473 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d421, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5327 pattern childGuard
    simpa only [d421, d473, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d421, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5343 pattern childGuard
    simpa only [d421, d473, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5345 (pattern : Twelve) (guard : d1870 pattern = 1) : d424 pattern ≤ (0 : Int) + d476 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d424, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5324 pattern childGuard
    simpa only [d424, d476, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d424, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5344 pattern childGuard
    simpa only [d424, d476, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5346 (pattern : Twelve) (guard : d0 pattern = 1) : d1030 pattern ≤ (0 : Int) + d186 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5347 (pattern : Twelve) (guard : d1870 pattern = 1) : d1038 pattern ≤ (0 : Int) + d426 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1038, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5248 pattern childGuard
    simpa only [d1870, d1038, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1038, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5346 pattern childGuard
    simpa only [d1870, d1038, d426, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5348 (pattern : Twelve) (guard : d1848 pattern = 1) : d1031 pattern ≤ (0 : Int) + d17 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5093 pattern childGuard
    simpa only [d1031, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5109 pattern childGuard
    simpa only [d1031, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5349 (pattern : Twelve) (guard : d0 pattern = 1) : d1032 pattern ≤ (0 : Int) + d908 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5350 (pattern : Twelve) (guard : d1870 pattern = 1) : d1039 pattern ≤ (0 : Int) + d1070 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1039, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5348 pattern childGuard
    simpa only [d1870, d1039, d1070, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1039, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5349 pattern childGuard
    simpa only [d1870, d1039, d1070, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5351 (pattern : Twelve) (guard : d1870 pattern = 1) : d1048 pattern ≤ (0 : Int) + d1078 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1048, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5347 pattern childGuard
    simpa only [d1048, d1078, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1048, d1078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5350 pattern childGuard
    simpa only [d1048, d1078, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5352 (pattern : Twelve) (guard : d1848 pattern = 1) : d377 pattern ≤ (0 : Int) + d56 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d377, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4979 pattern childGuard
    simpa only [d377, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d377, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2566 pattern childGuard
    simpa only [d377, d56, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5353 (pattern : Twelve) (guard : d0 pattern = 1) : d1033 pattern ≤ (0 : Int) + d189 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5354 (pattern : Twelve) (guard : d1870 pattern = 1) : d1040 pattern ≤ (0 : Int) + d1071 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1040, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5352 pattern childGuard
    simpa only [d1870, d1040, d1071, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1040, d1071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5353 pattern childGuard
    simpa only [d1870, d1040, d1071, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5355 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d827 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2752 pattern childGuard
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5356 (pattern : Twelve) (guard : d0 pattern = 1) : d1032 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5357 (pattern : Twelve) (guard : d1870 pattern = 1) : d1041 pattern ≤ (0 : Int) + d1072 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1041, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5355 pattern childGuard
    simpa only [d1870, d1041, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1041, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5356 pattern childGuard
    simpa only [d1870, d1041, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5358 (pattern : Twelve) (guard : d1870 pattern = 1) : d1049 pattern ≤ (0 : Int) + d1079 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1049, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5354 pattern childGuard
    simpa only [d1049, d1079, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1049, d1079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5357 pattern childGuard
    simpa only [d1049, d1079, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5359 (pattern : Twelve) (guard : d1870 pattern = 1) : d1054 pattern ≤ (0 : Int) + d1088 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1054, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5351 pattern childGuard
    simpa only [d1054, d1088, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1054, d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5358 pattern childGuard
    simpa only [d1054, d1088, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5360 (pattern : Twelve) (guard : d1870 pattern = 1) : d1040 pattern ≤ (0 : Int) + d430 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1040, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5265 pattern childGuard
    simpa only [d1870, d1040, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1040, d430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5353 pattern childGuard
    simpa only [d1870, d1040, d430, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5361 (pattern : Twelve) (guard : d1870 pattern = 1) : d1041 pattern ≤ (0 : Int) + d1073 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1041, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5109 pattern childGuard
    simpa only [d1870, d1041, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1041, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5356 pattern childGuard
    simpa only [d1870, d1041, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5362 (pattern : Twelve) (guard : d1870 pattern = 1) : d1049 pattern ≤ (0 : Int) + d1080 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1049, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5360 pattern childGuard
    simpa only [d1049, d1080, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1049, d1080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5361 pattern childGuard
    simpa only [d1049, d1080, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5363 (pattern : Twelve) (guard : d0 pattern = 1) : d1033 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5364 (pattern : Twelve) (guard : d1870 pattern = 1) : d1042 pattern ≤ (0 : Int) + d432 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1042, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5271 pattern childGuard
    simpa only [d1870, d1042, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1042, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5363 pattern childGuard
    simpa only [d1870, d1042, d432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5365 (pattern : Twelve) (guard : d1870 pattern = 1) : d1050 pattern ≤ (0 : Int) + d1081 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1050, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5364 pattern childGuard
    simpa only [d1050, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1050, d1081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5357 pattern childGuard
    simpa only [d1050, d1081, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5366 (pattern : Twelve) (guard : d1870 pattern = 1) : d1055 pattern ≤ (0 : Int) + d1089 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1055, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5362 pattern childGuard
    simpa only [d1055, d1089, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1055, d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5365 pattern childGuard
    simpa only [d1055, d1089, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5367 (pattern : Twelve) (guard : d1870 pattern = 1) : d1060 pattern ≤ (0 : Int) + d1095 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1060, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5359 pattern childGuard
    simpa only [d1060, d1095, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1060, d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5366 pattern childGuard
    simpa only [d1060, d1095, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5368 (pattern : Twelve) (guard : d0 pattern = 1) : d1033 pattern ≤ (0 : Int) + d194 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5369 (pattern : Twelve) (guard : d1870 pattern = 1) : d1043 pattern ≤ (0 : Int) + d434 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1043, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5280 pattern childGuard
    simpa only [d1870, d1043, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1043, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5368 pattern childGuard
    simpa only [d1870, d1043, d434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5370 (pattern : Twelve) (guard : d1870 pattern = 1) : d1041 pattern ≤ (0 : Int) + d1074 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1041, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d1870, d1041, d1074, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1041, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5356 pattern childGuard
    simpa only [d1870, d1041, d1074, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5371 (pattern : Twelve) (guard : d1870 pattern = 1) : d1051 pattern ≤ (0 : Int) + d1082 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1051, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5369 pattern childGuard
    simpa only [d1051, d1082, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1051, d1082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5370 pattern childGuard
    simpa only [d1051, d1082, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5372 (pattern : Twelve) (guard : d0 pattern = 1) : d1034 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5373 (pattern : Twelve) (guard : d1870 pattern = 1) : d1044 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1044, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d1870, d1044, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1044, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5372 pattern childGuard
    simpa only [d1870, d1044, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5374 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (0 : Int) + d830 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5034 pattern childGuard
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2768 pattern childGuard
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5375 (pattern : Twelve) (guard : d0 pattern = 1) : d1035 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5376 (pattern : Twelve) (guard : d1870 pattern = 1) : d1045 pattern ≤ (0 : Int) + d1075 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1045, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5374 pattern childGuard
    simpa only [d1870, d1045, d1075, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1045, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5375 pattern childGuard
    simpa only [d1870, d1045, d1075, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5377 (pattern : Twelve) (guard : d1870 pattern = 1) : d1052 pattern ≤ (0 : Int) + d1083 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1052, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5373 pattern childGuard
    simpa only [d1052, d1083, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1052, d1083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5376 pattern childGuard
    simpa only [d1052, d1083, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5378 (pattern : Twelve) (guard : d1870 pattern = 1) : d1056 pattern ≤ (0 : Int) + d1090 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1056, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5371 pattern childGuard
    simpa only [d1056, d1090, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1056, d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5377 pattern childGuard
    simpa only [d1056, d1090, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5379 (pattern : Twelve) (guard : d1870 pattern = 1) : d1057 pattern ≤ (0 : Int) + d1091 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1057, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5365 pattern childGuard
    simpa only [d1057, d1091, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1057, d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5294 pattern childGuard
    simpa only [d1057, d1091, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5380 (pattern : Twelve) (guard : d1870 pattern = 1) : d1061 pattern ≤ (0 : Int) + d1096 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1061, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5378 pattern childGuard
    simpa only [d1061, d1096, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1061, d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5379 pattern childGuard
    simpa only [d1061, d1096, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5381 (pattern : Twelve) (guard : d1870 pattern = 1) : d1064 pattern ≤ (0 : Int) + d1099 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1064, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5367 pattern childGuard
    simpa only [d1064, d1099, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1064, d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5380 pattern childGuard
    simpa only [d1064, d1099, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5382 (pattern : Twelve) (guard : d1870 pattern = 1) : d1042 pattern ≤ (0 : Int) + d438 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1042, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5045 pattern childGuard
    simpa only [d1870, d1042, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1042, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5363 pattern childGuard
    simpa only [d1870, d1042, d438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5383 (pattern : Twelve) (guard : d1870 pattern = 1) : d1050 pattern ≤ (0 : Int) + d1084 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1050, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5382 pattern childGuard
    simpa only [d1050, d1084, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1050, d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5361 pattern childGuard
    simpa only [d1050, d1084, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5384 (pattern : Twelve) (guard : d1870 pattern = 1) : d1050 pattern ≤ (0 : Int) + d1092 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5383 pattern childGuard
    simpa only [d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5365 pattern childGuard
    simpa only [d1092, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5385 (pattern : Twelve) (guard : d1870 pattern = 1) : d1042 pattern ≤ (0 : Int) + d441 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1042, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5006 pattern childGuard
    simpa only [d1870, d1042, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1042, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5363 pattern childGuard
    simpa only [d1870, d1042, d441, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5386 (pattern : Twelve) (guard : d1870 pattern = 1) : d1050 pattern ≤ (0 : Int) + d1085 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1050, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5385 pattern childGuard
    simpa only [d1050, d1085, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1050, d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5370 pattern childGuard
    simpa only [d1050, d1085, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5387 (pattern : Twelve) (guard : d1870 pattern = 1) : d1058 pattern ≤ (0 : Int) + d1093 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1058, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5386 pattern childGuard
    simpa only [d1058, d1093, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1058, d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5377 pattern childGuard
    simpa only [d1058, d1093, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5388 (pattern : Twelve) (guard : d1870 pattern = 1) : d1062 pattern ≤ (0 : Int) + d1097 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1062, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5387 pattern childGuard
    simpa only [d1062, d1097, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1062, d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5379 pattern childGuard
    simpa only [d1062, d1097, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5389 (pattern : Twelve) (guard : d1870 pattern = 1) : d1065 pattern ≤ (0 : Int) + d1100 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1065, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5384 pattern childGuard
    simpa only [d1065, d1100, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1065, d1100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5388 pattern childGuard
    simpa only [d1065, d1100, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5390 (pattern : Twelve) (guard : d1870 pattern = 1) : d1067 pattern ≤ (0 : Int) + d1102 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1067, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5381 pattern childGuard
    simpa only [d1067, d1102, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1067, d1102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5389 pattern childGuard
    simpa only [d1067, d1102, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5391 (pattern : Twelve) (guard : d1870 pattern = 1) : d1068 pattern ≤ (0 : Int) + d1103 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1068, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5390 pattern childGuard
    simpa only [d1068, d1103, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1068, d1103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5389 pattern childGuard
    simpa only [d1068, d1103, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5392 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d119 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5393 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d879 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d36, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d36, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d36, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5392 pattern childGuard
    simpa only [d1848, d36, d879, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5394 (pattern : Twelve) (guard : d1848 pattern = 1) : d36 pattern ≤ (0 : Int) + d886 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5393 pattern childGuard
    simpa only [d886, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5395 (pattern : Twelve) (guard : d1870 pattern = 1) : d1041 pattern ≤ (0 : Int) + d1076 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1041, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5394 pattern childGuard
    simpa only [d1870, d1041, d1076, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1041, d1076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5356 pattern childGuard
    simpa only [d1870, d1041, d1076, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5396 (pattern : Twelve) (guard : d1870 pattern = 1) : d1050 pattern ≤ (0 : Int) + d1086 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1050, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5385 pattern childGuard
    simpa only [d1050, d1086, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1050, d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5395 pattern childGuard
    simpa only [d1050, d1086, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5397 (pattern : Twelve) (guard : d0 pattern = 1) : d1036 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5398 (pattern : Twelve) (guard : d1870 pattern = 1) : d1046 pattern ≤ (0 : Int) + d436 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1046, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5284 pattern childGuard
    simpa only [d1870, d1046, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1046, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5397 pattern childGuard
    simpa only [d1870, d1046, d436, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5399 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d118 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5400 (pattern : Twelve) (guard : d1848 pattern = 1) : d40 pattern ≤ (0 : Int) + d881 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d40, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1340 pattern childGuard
    simpa only [d1848, d40, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d40, d881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5399 pattern childGuard
    simpa only [d1848, d40, d881, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5401 (pattern : Twelve) (guard : d1848 pattern = 1) : d125 pattern ≤ (0 : Int) + d125 pattern := by
  omega
theorem c5402 (pattern : Twelve) (guard : d1848 pattern = 1) : d1037 pattern ≤ (0 : Int) + d888 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1037, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5400 pattern childGuard
    simpa only [d1037, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1037, d888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5401 pattern childGuard
    simpa only [d1037, d888, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5403 (pattern : Twelve) (guard : d0 pattern = 1) : d889 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5404 (pattern : Twelve) (guard : d1870 pattern = 1) : d1047 pattern ≤ (0 : Int) + d1077 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1047, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5402 pattern childGuard
    simpa only [d1870, d1047, d1077, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1047, d1077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5403 pattern childGuard
    simpa only [d1870, d1047, d1077, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5405 (pattern : Twelve) (guard : d1870 pattern = 1) : d1053 pattern ≤ (0 : Int) + d1087 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1053, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5398 pattern childGuard
    simpa only [d1053, d1087, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1053, d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5404 pattern childGuard
    simpa only [d1053, d1087, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5406 (pattern : Twelve) (guard : d1870 pattern = 1) : d1059 pattern ≤ (0 : Int) + d1094 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1059, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5396 pattern childGuard
    simpa only [d1059, d1094, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1059, d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5405 pattern childGuard
    simpa only [d1059, d1094, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5407 (pattern : Twelve) (guard : d1870 pattern = 1) : d1063 pattern ≤ (0 : Int) + d1098 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1063, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5406 pattern childGuard
    simpa only [d1063, d1098, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1063, d1098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5379 pattern childGuard
    simpa only [d1063, d1098, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5408 (pattern : Twelve) (guard : d1870 pattern = 1) : d1066 pattern ≤ (0 : Int) + d1101 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1066, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5384 pattern childGuard
    simpa only [d1066, d1101, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1066, d1101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5407 pattern childGuard
    simpa only [d1066, d1101, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5409 (pattern : Twelve) (guard : d1870 pattern = 1) : d1069 pattern ≤ (0 : Int) + d1104 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1069, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5391 pattern childGuard
    simpa only [d1069, d1104, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1069, d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5408 pattern childGuard
    simpa only [d1069, d1104, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5410 (pattern : Twelve) (guard : d0 pattern = 1) : d1445 pattern ≤ (0 : Int) + d908 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5411 (pattern : Twelve) (guard : d1870 pattern = 1) : d1448 pattern ≤ (0 : Int) + d1070 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1448, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5348 pattern childGuard
    simpa only [d1870, d1448, d1070, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1448, d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5410 pattern childGuard
    simpa only [d1870, d1448, d1070, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5412 (pattern : Twelve) (guard : d1870 pattern = 1) : d1449 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1449, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5162 pattern childGuard
    simpa only [d1870, d1449, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1449, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1870, d1449, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5413 (pattern : Twelve) (guard : d1870 pattern = 1) : d1455 pattern ≤ (0 : Int) + d1472 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1455, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5411 pattern childGuard
    simpa only [d1455, d1472, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1455, d1472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5412 pattern childGuard
    simpa only [d1455, d1472, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5414 (pattern : Twelve) (guard : d0 pattern = 1) : d1445 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5415 (pattern : Twelve) (guard : d1870 pattern = 1) : d1450 pattern ≤ (0 : Int) + d1072 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1450, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5355 pattern childGuard
    simpa only [d1870, d1450, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1450, d1072, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5414 pattern childGuard
    simpa only [d1870, d1450, d1072, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5416 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (0 : Int) + d1286 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5096 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2795 pattern childGuard
    simpa only [d1286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5417 (pattern : Twelve) (guard : d1870 pattern = 1) : d1449 pattern ≤ (0 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1449, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5416 pattern childGuard
    simpa only [d1870, d1449, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1449, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1870, d1449, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5418 (pattern : Twelve) (guard : d1870 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1473 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1456, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5415 pattern childGuard
    simpa only [d1456, d1473, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1456, d1473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5417 pattern childGuard
    simpa only [d1456, d1473, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5419 (pattern : Twelve) (guard : d1870 pattern = 1) : d1459 pattern ≤ (0 : Int) + d1479 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1459, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5413 pattern childGuard
    simpa only [d1459, d1479, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1459, d1479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5418 pattern childGuard
    simpa only [d1459, d1479, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5420 (pattern : Twelve) (guard : d1870 pattern = 1) : d1450 pattern ≤ (0 : Int) + d1073 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1450, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5109 pattern childGuard
    simpa only [d1870, d1450, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1450, d1073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5414 pattern childGuard
    simpa only [d1870, d1450, d1073, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5421 (pattern : Twelve) (guard : d1870 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1474 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1456, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5420 pattern childGuard
    simpa only [d1456, d1474, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1456, d1474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5412 pattern childGuard
    simpa only [d1456, d1474, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5422 (pattern : Twelve) (guard : d1870 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1480 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5421 pattern childGuard
    simpa only [d1480, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5418 pattern childGuard
    simpa only [d1480, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5423 (pattern : Twelve) (guard : d1870 pattern = 1) : d1463 pattern ≤ (0 : Int) + d1484 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1463, d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5419 pattern childGuard
    simpa only [d1463, d1484, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1463, d1484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5422 pattern childGuard
    simpa only [d1463, d1484, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5424 (pattern : Twelve) (guard : d1870 pattern = 1) : d1450 pattern ≤ (0 : Int) + d1074 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1450, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4985 pattern childGuard
    simpa only [d1870, d1450, d1074, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1450, d1074, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5414 pattern childGuard
    simpa only [d1870, d1450, d1074, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5425 (pattern : Twelve) (guard : d1870 pattern = 1) : d1449 pattern ≤ (0 : Int) + d1298 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1449, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5096 pattern childGuard
    simpa only [d1870, d1449, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1449, d1298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1870, d1449, d1298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5426 (pattern : Twelve) (guard : d1870 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1475 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1456, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5424 pattern childGuard
    simpa only [d1456, d1475, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1456, d1475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5425 pattern childGuard
    simpa only [d1456, d1475, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5427 (pattern : Twelve) (guard : d0 pattern = 1) : d1446 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5428 (pattern : Twelve) (guard : d1870 pattern = 1) : d1451 pattern ≤ (0 : Int) + d1075 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1451, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5374 pattern childGuard
    simpa only [d1870, d1451, d1075, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1451, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5427 pattern childGuard
    simpa only [d1870, d1451, d1075, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5429 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (0 : Int) + d1289 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5123 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2806 pattern childGuard
    simpa only [d1289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5430 (pattern : Twelve) (guard : d1870 pattern = 1) : d1452 pattern ≤ (0 : Int) + d1300 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1452, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5429 pattern childGuard
    simpa only [d1870, d1452, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1452, d1300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1870, d1452, d1300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5431 (pattern : Twelve) (guard : d1870 pattern = 1) : d1457 pattern ≤ (0 : Int) + d1476 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1457, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5428 pattern childGuard
    simpa only [d1457, d1476, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1457, d1476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5430 pattern childGuard
    simpa only [d1457, d1476, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5432 (pattern : Twelve) (guard : d1870 pattern = 1) : d1460 pattern ≤ (0 : Int) + d1481 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1460, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5426 pattern childGuard
    simpa only [d1460, d1481, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1460, d1481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5431 pattern childGuard
    simpa only [d1460, d1481, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5433 (pattern : Twelve) (guard : d1870 pattern = 1) : d1461 pattern ≤ (0 : Int) + d1482 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1461, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5418 pattern childGuard
    simpa only [d1461, d1482, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1461, d1482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5294 pattern childGuard
    simpa only [d1461, d1482, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5434 (pattern : Twelve) (guard : d1870 pattern = 1) : d1464 pattern ≤ (0 : Int) + d1485 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1464, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5432 pattern childGuard
    simpa only [d1464, d1485, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1464, d1485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5433 pattern childGuard
    simpa only [d1464, d1485, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5435 (pattern : Twelve) (guard : d1870 pattern = 1) : d1466 pattern ≤ (0 : Int) + d1487 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1466, d1487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5423 pattern childGuard
    simpa only [d1466, d1487, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1466, d1487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5434 pattern childGuard
    simpa only [d1466, d1487, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5436 (pattern : Twelve) (guard : d1870 pattern = 1) : d1467 pattern ≤ (0 : Int) + d1488 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1467, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5422 pattern childGuard
    simpa only [d1467, d1488, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1467, d1488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5434 pattern childGuard
    simpa only [d1467, d1488, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5437 (pattern : Twelve) (guard : d1870 pattern = 1) : d1469 pattern ≤ (0 : Int) + d1490 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1469, d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5435 pattern childGuard
    simpa only [d1469, d1490, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1469, d1490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5436 pattern childGuard
    simpa only [d1469, d1490, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5438 (pattern : Twelve) (guard : d1870 pattern = 1) : d1470 pattern ≤ (0 : Int) + d1491 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1470, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5437 pattern childGuard
    simpa only [d1470, d1491, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1470, d1491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5436 pattern childGuard
    simpa only [d1470, d1491, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5439 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (0 : Int) + d1329 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d29, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c328 pattern childGuard
    simpa only [d1848, d29, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d29, d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5218 pattern childGuard
    simpa only [d1848, d29, d1329, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5440 (pattern : Twelve) (guard : d1848 pattern = 1) : d29 pattern ≤ (0 : Int) + d1336 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5096 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5439 pattern childGuard
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5441 (pattern : Twelve) (guard : d1870 pattern = 1) : d1449 pattern ≤ (0 : Int) + d1342 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1449, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5440 pattern childGuard
    simpa only [d1870, d1449, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1449, d1342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1870, d1449, d1342, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5442 (pattern : Twelve) (guard : d1870 pattern = 1) : d1456 pattern ≤ (0 : Int) + d1477 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1456, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5424 pattern childGuard
    simpa only [d1456, d1477, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1456, d1477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5441 pattern childGuard
    simpa only [d1456, d1477, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5443 (pattern : Twelve) (guard : d0 pattern = 1) : d1337 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c5444 (pattern : Twelve) (guard : d1870 pattern = 1) : d1453 pattern ≤ (0 : Int) + d1075 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1453, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5374 pattern childGuard
    simpa only [d1870, d1453, d1075, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1453, d1075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5443 pattern childGuard
    simpa only [d1870, d1453, d1075, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5445 (pattern : Twelve) (guard : d1848 pattern = 1) : d42 pattern ≤ (0 : Int) + d1332 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d42, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c392 pattern childGuard
    simpa only [d1848, d42, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d42, d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5224 pattern childGuard
    simpa only [d1848, d42, d1332, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5446 (pattern : Twelve) (guard : d1848 pattern = 1) : d128 pattern ≤ (0 : Int) + d128 pattern := by
  omega
theorem c5447 (pattern : Twelve) (guard : d1848 pattern = 1) : d1447 pattern ≤ (0 : Int) + d1338 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1447, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5445 pattern childGuard
    simpa only [d1447, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1447, d1338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5446 pattern childGuard
    simpa only [d1447, d1338, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5448 (pattern : Twelve) (guard : d1870 pattern = 1) : d1454 pattern ≤ (0 : Int) + d1344 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1454, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5447 pattern childGuard
    simpa only [d1870, d1454, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1454, d1344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1870, d1454, d1344, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5449 (pattern : Twelve) (guard : d1870 pattern = 1) : d1458 pattern ≤ (0 : Int) + d1478 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1458, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5444 pattern childGuard
    simpa only [d1458, d1478, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1458, d1478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5448 pattern childGuard
    simpa only [d1458, d1478, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5450 (pattern : Twelve) (guard : d1870 pattern = 1) : d1462 pattern ≤ (0 : Int) + d1483 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1462, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5442 pattern childGuard
    simpa only [d1462, d1483, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1462, d1483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5449 pattern childGuard
    simpa only [d1462, d1483, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5451 (pattern : Twelve) (guard : d1870 pattern = 1) : d1465 pattern ≤ (0 : Int) + d1486 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1465, d1486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5450 pattern childGuard
    simpa only [d1465, d1486, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1465, d1486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5433 pattern childGuard
    simpa only [d1465, d1486, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5452 (pattern : Twelve) (guard : d1870 pattern = 1) : d1468 pattern ≤ (0 : Int) + d1489 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1468, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5422 pattern childGuard
    simpa only [d1468, d1489, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1468, d1489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5451 pattern childGuard
    simpa only [d1468, d1489, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5453 (pattern : Twelve) (guard : d1870 pattern = 1) : d1471 pattern ≤ (0 : Int) + d1492 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1471, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5438 pattern childGuard
    simpa only [d1471, d1492, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1471, d1492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5452 pattern childGuard
    simpa only [d1471, d1492, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5454 (pattern : Twelve) (guard : d1870 pattern = 1) : d1716 pattern ≤ (0 : Int) + d1294 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1716, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5162 pattern childGuard
    simpa only [d1870, d1716, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1716, d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d1870, d1716, d1294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5455 (pattern : Twelve) (guard : d1870 pattern = 1) : d1452 pattern ≤ (0 : Int) + d1650 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1452, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5214 pattern childGuard
    simpa only [d1870, d1452, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1452, d1650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1870, d1452, d1650, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5456 (pattern : Twelve) (guard : d1870 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1730 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1719, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5454 pattern childGuard
    simpa only [d1719, d1730, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1719, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5455 pattern childGuard
    simpa only [d1719, d1730, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5457 (pattern : Twelve) (guard : d1870 pattern = 1) : d1716 pattern ≤ (0 : Int) + d1296 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1870, d1716, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5416 pattern childGuard
    simpa only [d1870, d1716, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1870, d1716, d1296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c398 pattern childGuard
    simpa only [d1870, d1716, d1296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5458 (pattern : Twelve) (guard : d1870 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1731 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1719, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5457 pattern childGuard
    simpa only [d1719, d1731, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1719, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5430 pattern childGuard
    simpa only [d1719, d1731, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c5459 (pattern : Twelve) (guard : d1870 pattern = 1) : d1719 pattern ≤ (0 : Int) + d1736 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5456 pattern childGuard
    simpa only [d1736, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1870 pattern = 1 := by simpa only [d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c5458 pattern childGuard
    simpa only [d1736, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
