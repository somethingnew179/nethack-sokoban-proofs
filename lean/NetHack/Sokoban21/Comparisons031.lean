/- Stage-only soko2-1 finite certificate. Kernel proof, proposeruntrusted. -/
import NetHack.Sokoban21.Comparisons030
set_option maxRecDepth 2048
set_option linter.unusedVariables false
namespace NetHack.Sokoban21.Diagram
theorem c4340 (pattern : Twelve) (guard : d1868 pattern = 1) : d360 pattern ≤ (0 : Int) + d347 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4338 pattern childGuard
    simpa only [d1868, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4339 pattern childGuard
    simpa only [d1868, d347, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4341 (pattern : Twelve) (guard : d1868 pattern = 1) : d363 pattern ≤ (0 : Int) + d349 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d363, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4340 pattern childGuard
    simpa only [d363, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d363, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4332 pattern childGuard
    simpa only [d363, d349, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4342 (pattern : Twelve) (guard : d1868 pattern = 1) : d364 pattern ≤ (0 : Int) + d350 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d364, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4333 pattern childGuard
    simpa only [d364, d350, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d364, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4341 pattern childGuard
    simpa only [d364, d350, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4343 (pattern : Twelve) (guard : d1868 pattern = 1) : d365 pattern ≤ (0 : Int) + d351 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d365, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4342 pattern childGuard
    simpa only [d365, d351, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d365, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4341 pattern childGuard
    simpa only [d365, d351, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4344 (pattern : Twelve) (guard : d0 pattern = 1) : d913 pattern ≤ (0 : Int) + d854 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4345 (pattern : Twelve) (guard : d1844 pattern = 1) : d1018 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1018, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c756 pattern childGuard
    simpa only [d1844, d1018, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1018, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4344 pattern childGuard
    simpa only [d1844, d1018, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4346 (pattern : Twelve) (guard : d0 pattern = 1) : d914 pattern ≤ (0 : Int) + d854 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4347 (pattern : Twelve) (guard : d1844 pattern = 1) : d1019 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1019, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c756 pattern childGuard
    simpa only [d1844, d1019, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1019, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4346 pattern childGuard
    simpa only [d1844, d1019, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4348 (pattern : Twelve) (guard : d1844 pattern = 1) : d1023 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4345 pattern childGuard
    simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4347 pattern childGuard
    simpa only [d1023, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4349 (pattern : Twelve) (guard : d0 pattern = 1) : d1024 pattern ≤ (0 : Int) + d922 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4350 (pattern : Twelve) (guard : d1868 pattern = 1) : d1025 pattern ≤ (0 : Int) + d1011 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1025, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4348 pattern childGuard
    simpa only [d1868, d1025, d1011, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1025, d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4349 pattern childGuard
    simpa only [d1868, d1025, d1011, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4351 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d858 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4352 (pattern : Twelve) (guard : d1844 pattern = 1) : d1022 pattern ≤ (0 : Int) + d864 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1022, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c763 pattern childGuard
    simpa only [d1844, d1022, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1022, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4351 pattern childGuard
    simpa only [d1844, d1022, d864, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4353 (pattern : Twelve) (guard : d0 pattern = 1) : d1022 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4354 (pattern : Twelve) (guard : d1868 pattern = 1) : d1022 pattern ≤ (0 : Int) + d1012 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4352 pattern childGuard
    simpa only [d1868, d1012, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4353 pattern childGuard
    simpa only [d1868, d1012, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4355 (pattern : Twelve) (guard : d1868 pattern = 1) : d1026 pattern ≤ (0 : Int) + d1014 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1026, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4350 pattern childGuard
    simpa only [d1026, d1014, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1026, d1014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4354 pattern childGuard
    simpa only [d1026, d1014, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4356 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d854 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4357 (pattern : Twelve) (guard : d1844 pattern = 1) : d1021 pattern ≤ (0 : Int) + d861 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1021, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c756 pattern childGuard
    simpa only [d1844, d1021, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1021, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4356 pattern childGuard
    simpa only [d1844, d1021, d861, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4358 (pattern : Twelve) (guard : d0 pattern = 1) : d1021 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4359 (pattern : Twelve) (guard : d1868 pattern = 1) : d1021 pattern ≤ (0 : Int) + d1013 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4357 pattern childGuard
    simpa only [d1868, d1013, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4358 pattern childGuard
    simpa only [d1868, d1013, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4360 (pattern : Twelve) (guard : d1868 pattern = 1) : d1027 pattern ≤ (0 : Int) + d1015 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1027, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4359 pattern childGuard
    simpa only [d1027, d1015, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1027, d1015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4354 pattern childGuard
    simpa only [d1027, d1015, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4361 (pattern : Twelve) (guard : d1868 pattern = 1) : d1028 pattern ≤ (0 : Int) + d1016 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1028, d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4355 pattern childGuard
    simpa only [d1028, d1016, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1028, d1016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4360 pattern childGuard
    simpa only [d1028, d1016, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4362 (pattern : Twelve) (guard : d1868 pattern = 1) : d1029 pattern ≤ (0 : Int) + d1017 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1029, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4361 pattern childGuard
    simpa only [d1029, d1017, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1029, d1017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4360 pattern childGuard
    simpa only [d1029, d1017, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4363 (pattern : Twelve) (guard : d0 pattern = 1) : d1357 pattern ≤ (0 : Int) + d1306 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4364 (pattern : Twelve) (guard : d1844 pattern = 1) : d1435 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1435, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c780 pattern childGuard
    simpa only [d1844, d1435, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1435, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4363 pattern childGuard
    simpa only [d1844, d1435, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4365 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1306 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4366 (pattern : Twelve) (guard : d1844 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1436, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c780 pattern childGuard
    simpa only [d1844, d1436, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1436, d1313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4365 pattern childGuard
    simpa only [d1844, d1436, d1313, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4367 (pattern : Twelve) (guard : d1844 pattern = 1) : d1438 pattern ≤ (0 : Int) + d1313 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4364 pattern childGuard
    simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4366 pattern childGuard
    simpa only [d1438, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4368 (pattern : Twelve) (guard : d0 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1363 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4369 (pattern : Twelve) (guard : d1868 pattern = 1) : d1439 pattern ≤ (0 : Int) + d1428 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1439, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4367 pattern childGuard
    simpa only [d1868, d1439, d1428, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1439, d1428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4368 pattern childGuard
    simpa only [d1868, d1439, d1428, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4370 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1310 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4371 (pattern : Twelve) (guard : d1844 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1316 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1437, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c787 pattern childGuard
    simpa only [d1844, d1437, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1437, d1316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4370 pattern childGuard
    simpa only [d1844, d1437, d1316, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4372 (pattern : Twelve) (guard : d0 pattern = 1) : d1437 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4373 (pattern : Twelve) (guard : d1868 pattern = 1) : d1437 pattern ≤ (0 : Int) + d1429 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4371 pattern childGuard
    simpa only [d1868, d1429, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4372 pattern childGuard
    simpa only [d1868, d1429, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4374 (pattern : Twelve) (guard : d1868 pattern = 1) : d1440 pattern ≤ (0 : Int) + d1431 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1440, d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4369 pattern childGuard
    simpa only [d1440, d1431, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1440, d1431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4373 pattern childGuard
    simpa only [d1440, d1431, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4375 (pattern : Twelve) (guard : d0 pattern = 1) : d1436 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4376 (pattern : Twelve) (guard : d1868 pattern = 1) : d1436 pattern ≤ (0 : Int) + d1430 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4366 pattern childGuard
    simpa only [d1868, d1430, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4375 pattern childGuard
    simpa only [d1868, d1430, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4377 (pattern : Twelve) (guard : d1868 pattern = 1) : d1441 pattern ≤ (0 : Int) + d1432 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1441, d1432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4376 pattern childGuard
    simpa only [d1441, d1432, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1441, d1432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4373 pattern childGuard
    simpa only [d1441, d1432, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4378 (pattern : Twelve) (guard : d1868 pattern = 1) : d1442 pattern ≤ (0 : Int) + d1433 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1442, d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4374 pattern childGuard
    simpa only [d1442, d1433, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1442, d1433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4377 pattern childGuard
    simpa only [d1442, d1433, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4379 (pattern : Twelve) (guard : d1868 pattern = 1) : d1443 pattern ≤ (0 : Int) + d1434 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1443, d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4378 pattern childGuard
    simpa only [d1443, d1434, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1868 pattern = 1 := by simpa only [d1443, d1434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4377 pattern childGuard
    simpa only [d1443, d1434, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4380 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d1657 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4381 (pattern : Twelve) (guard : d1844 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1660 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1844, d1715, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c803 pattern childGuard
    simpa only [d1844, d1715, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1844, d1715, d1660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4380 pattern childGuard
    simpa only [d1844, d1715, d1660, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4382 (pattern : Twelve) (guard : d0 pattern = 1) : d1715 pattern ≤ (0 : Int) + d6 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4383 (pattern : Twelve) (guard : d1868 pattern = 1) : d1715 pattern ≤ (0 : Int) + d1714 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1844 pattern = 1 := by simpa only [d1868, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4381 pattern childGuard
    simpa only [d1868, d1714, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1868, d1714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4382 pattern childGuard
    simpa only [d1868, d1714, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4384 (pattern : Twelve) (guard : d1849 pattern = 1) : d0 pattern ≤ (0 : Int) + d235 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d1849, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c79 pattern childGuard
    simpa only [d1849, d235, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4385 (pattern : Twelve) (guard : d1849 pattern = 1) : d50 pattern ≤ (0 : Int) + d236 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d50, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1827 pattern childGuard
    simpa only [d1849, d50, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d50, d236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c82 pattern childGuard
    simpa only [d1849, d50, d236, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4386 (pattern : Twelve) (guard : d1849 pattern = 1) : d72 pattern ≤ (0 : Int) + d256 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d72, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4384 pattern childGuard
    simpa only [d72, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d72, d256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4385 pattern childGuard
    simpa only [d72, d256, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4387 (pattern : Twelve) (guard : d1849 pattern = 1) : d0 pattern ≤ (0 : Int) + d237 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d1849, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c85 pattern childGuard
    simpa only [d1849, d237, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4388 (pattern : Twelve) (guard : d1849 pattern = 1) : d51 pattern ≤ (0 : Int) + d238 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d51, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1830 pattern childGuard
    simpa only [d1849, d51, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d51, d238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c88 pattern childGuard
    simpa only [d1849, d51, d238, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4389 (pattern : Twelve) (guard : d1849 pattern = 1) : d73 pattern ≤ (0 : Int) + d257 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d73, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4387 pattern childGuard
    simpa only [d73, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d73, d257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4388 pattern childGuard
    simpa only [d73, d257, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4390 (pattern : Twelve) (guard : d1849 pattern = 1) : d91 pattern ≤ (0 : Int) + d272 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d91, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4386 pattern childGuard
    simpa only [d91, d272, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d91, d272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4389 pattern childGuard
    simpa only [d91, d272, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4391 (pattern : Twelve) (guard : d0 pattern = 1) : d208 pattern ≤ (0 : Int) + d273 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4392 (pattern : Twelve) (guard : d1857 pattern = 1) : d352 pattern ≤ (0 : Int) + d284 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d352, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4390 pattern childGuard
    simpa only [d1857, d352, d284, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d352, d284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4391 pattern childGuard
    simpa only [d1857, d352, d284, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4393 (pattern : Twelve) (guard : d1849 pattern = 1) : d0 pattern ≤ (0 : Int) + d242 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d1849, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c106 pattern childGuard
    simpa only [d1849, d242, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4394 (pattern : Twelve) (guard : d1849 pattern = 1) : d50 pattern ≤ (0 : Int) + d243 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d50, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1827 pattern childGuard
    simpa only [d1849, d50, d243, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d50, d243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c108 pattern childGuard
    simpa only [d1849, d50, d243, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4395 (pattern : Twelve) (guard : d1849 pattern = 1) : d72 pattern ≤ (0 : Int) + d260 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d72, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4393 pattern childGuard
    simpa only [d72, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d72, d260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4394 pattern childGuard
    simpa only [d72, d260, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4396 (pattern : Twelve) (guard : d1849 pattern = 1) : d0 pattern ≤ (0 : Int) + d244 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d1849, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c111 pattern childGuard
    simpa only [d1849, d244, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4397 (pattern : Twelve) (guard : d1849 pattern = 1) : d55 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d55, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1676 pattern childGuard
    simpa only [d1849, d55, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d55, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c101 pattern childGuard
    simpa only [d1849, d55, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4398 (pattern : Twelve) (guard : d1849 pattern = 1) : d76 pattern ≤ (0 : Int) + d261 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d76, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4396 pattern childGuard
    simpa only [d76, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d76, d261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4397 pattern childGuard
    simpa only [d76, d261, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4399 (pattern : Twelve) (guard : d1849 pattern = 1) : d93 pattern ≤ (0 : Int) + d274 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d93, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4395 pattern childGuard
    simpa only [d93, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d93, d274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4398 pattern childGuard
    simpa only [d93, d274, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4400 (pattern : Twelve) (guard : d0 pattern = 1) : d209 pattern ≤ (0 : Int) + d275 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4401 (pattern : Twelve) (guard : d1857 pattern = 1) : d353 pattern ≤ (0 : Int) + d285 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d353, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4399 pattern childGuard
    simpa only [d1857, d353, d285, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d353, d285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4400 pattern childGuard
    simpa only [d1857, d353, d285, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4402 (pattern : Twelve) (guard : d1857 pattern = 1) : d358 pattern ≤ (0 : Int) + d293 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d358, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4392 pattern childGuard
    simpa only [d358, d293, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d358, d293, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4401 pattern childGuard
    simpa only [d358, d293, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4403 (pattern : Twelve) (guard : d1848 pattern = 1) : d0 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c2858 pattern childGuard
    simpa only [d1848, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4404 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d180 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4405 (pattern : Twelve) (guard : d1849 pattern = 1) : d0 pattern ≤ (0 : Int) + d247 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4403 pattern childGuard
    simpa only [d1849, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4404 pattern childGuard
    simpa only [d1849, d247, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4406 (pattern : Twelve) (guard : d0 pattern = 1) : d1 pattern ≤ (0 : Int) + d2 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4407 (pattern : Twelve) (guard : d1848 pattern = 1) : d26 pattern ≤ (0 : Int) + d30 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c78 pattern childGuard
    simpa only [d1848, d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4406 pattern childGuard
    simpa only [d1848, d26, d30, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4408 (pattern : Twelve) (guard : d0 pattern = 1) : d27 pattern ≤ (0 : Int) + d181 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4409 (pattern : Twelve) (guard : d1849 pattern = 1) : d50 pattern ≤ (0 : Int) + d248 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d50, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4407 pattern childGuard
    simpa only [d1849, d50, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d50, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4408 pattern childGuard
    simpa only [d1849, d50, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4410 (pattern : Twelve) (guard : d1849 pattern = 1) : d72 pattern ≤ (0 : Int) + d264 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d72, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4405 pattern childGuard
    simpa only [d72, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d72, d264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4409 pattern childGuard
    simpa only [d72, d264, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4411 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d181 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4412 (pattern : Twelve) (guard : d1849 pattern = 1) : d0 pattern ≤ (0 : Int) + d248 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4403 pattern childGuard
    simpa only [d1849, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4411 pattern childGuard
    simpa only [d1849, d248, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4413 (pattern : Twelve) (guard : d0 pattern = 1) : d18 pattern ≤ (0 : Int) + d23 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4414 (pattern : Twelve) (guard : d1848 pattern = 1) : d28 pattern ≤ (0 : Int) + d34 pattern := by
  cases selected : pattern.i with
  | false =>
    have childGuard : d1 pattern = 1 := by simpa only [d1848, d28, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c240 pattern childGuard
    simpa only [d1848, d28, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1848, d28, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4413 pattern childGuard
    simpa only [d1848, d28, d34, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4415 (pattern : Twelve) (guard : d1849 pattern = 1) : d51 pattern ≤ (0 : Int) + d241 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d51, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4414 pattern childGuard
    simpa only [d1849, d51, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d51, d241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c101 pattern childGuard
    simpa only [d1849, d51, d241, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4416 (pattern : Twelve) (guard : d1849 pattern = 1) : d73 pattern ≤ (0 : Int) + d265 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d73, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4412 pattern childGuard
    simpa only [d73, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d73, d265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4415 pattern childGuard
    simpa only [d73, d265, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4417 (pattern : Twelve) (guard : d1849 pattern = 1) : d91 pattern ≤ (0 : Int) + d276 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d91, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4410 pattern childGuard
    simpa only [d91, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d91, d276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4416 pattern childGuard
    simpa only [d91, d276, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4418 (pattern : Twelve) (guard : d0 pattern = 1) : d211 pattern ≤ (0 : Int) + d277 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4419 (pattern : Twelve) (guard : d1857 pattern = 1) : d354 pattern ≤ (0 : Int) + d286 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d354, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4417 pattern childGuard
    simpa only [d1857, d354, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d354, d286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4418 pattern childGuard
    simpa only [d1857, d354, d286, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4420 (pattern : Twelve) (guard : d0 pattern = 1) : d0 pattern ≤ (0 : Int) + d183 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4421 (pattern : Twelve) (guard : d1849 pattern = 1) : d0 pattern ≤ (0 : Int) + d252 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4403 pattern childGuard
    simpa only [d1849, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4420 pattern childGuard
    simpa only [d1849, d252, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4422 (pattern : Twelve) (guard : d1849 pattern = 1) : d50 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d50, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4407 pattern childGuard
    simpa only [d1849, d50, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d50, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c159 pattern childGuard
    simpa only [d1849, d50, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4423 (pattern : Twelve) (guard : d1849 pattern = 1) : d72 pattern ≤ (0 : Int) + d268 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d72, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4421 pattern childGuard
    simpa only [d72, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d72, d268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4422 pattern childGuard
    simpa only [d72, d268, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4424 (pattern : Twelve) (guard : d1849 pattern = 1) : d0 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4403 pattern childGuard
    simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c157 pattern childGuard
    simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4425 (pattern : Twelve) (guard : d1849 pattern = 1) : d76 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d76, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4424 pattern childGuard
    simpa only [d76, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d76, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4397 pattern childGuard
    simpa only [d76, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4426 (pattern : Twelve) (guard : d1849 pattern = 1) : d93 pattern ≤ (0 : Int) + d278 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d93, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4423 pattern childGuard
    simpa only [d93, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d93, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4425 pattern childGuard
    simpa only [d93, d278, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4427 (pattern : Twelve) (guard : d1857 pattern = 1) : d355 pattern ≤ (0 : Int) + d287 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d355, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4426 pattern childGuard
    simpa only [d1857, d355, d287, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d355, d287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1857, d355, d287, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4428 (pattern : Twelve) (guard : d1857 pattern = 1) : d359 pattern ≤ (0 : Int) + d294 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d359, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4419 pattern childGuard
    simpa only [d359, d294, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d359, d294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4427 pattern childGuard
    simpa only [d359, d294, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4429 (pattern : Twelve) (guard : d1857 pattern = 1) : d361 pattern ≤ (0 : Int) + d297 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d361, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4402 pattern childGuard
    simpa only [d361, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d361, d297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4428 pattern childGuard
    simpa only [d361, d297, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4430 (pattern : Twelve) (guard : d1849 pattern = 1) : d0 pattern ≤ (0 : Int) + d253 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1560 pattern childGuard
    simpa only [d1849, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c157 pattern childGuard
    simpa only [d1849, d253, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4431 (pattern : Twelve) (guard : d1849 pattern = 1) : d50 pattern ≤ (0 : Int) + d254 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d50, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1827 pattern childGuard
    simpa only [d1849, d50, d254, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d50, d254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c159 pattern childGuard
    simpa only [d1849, d50, d254, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4432 (pattern : Twelve) (guard : d1849 pattern = 1) : d72 pattern ≤ (0 : Int) + d269 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d72, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4430 pattern childGuard
    simpa only [d72, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d72, d269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4431 pattern childGuard
    simpa only [d72, d269, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4433 (pattern : Twelve) (guard : d1849 pattern = 1) : d30 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1567 pattern childGuard
    simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c162 pattern childGuard
    simpa only [d1849, d246, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4434 (pattern : Twelve) (guard : d1849 pattern = 1) : d80 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d80, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4433 pattern childGuard
    simpa only [d80, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d80, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4397 pattern childGuard
    simpa only [d80, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4435 (pattern : Twelve) (guard : d1849 pattern = 1) : d97 pattern ≤ (0 : Int) + d279 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d97, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4432 pattern childGuard
    simpa only [d97, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d97, d279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4434 pattern childGuard
    simpa only [d97, d279, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4436 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d280 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4437 (pattern : Twelve) (guard : d1857 pattern = 1) : d356 pattern ≤ (0 : Int) + d288 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d356, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4435 pattern childGuard
    simpa only [d1857, d356, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d356, d288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4436 pattern childGuard
    simpa only [d1857, d356, d288, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4438 (pattern : Twelve) (guard : d1849 pattern = 1) : d72 pattern ≤ (0 : Int) + d246 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4424 pattern childGuard
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4422 pattern childGuard
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4439 (pattern : Twelve) (guard : d1849 pattern = 1) : d97 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d97, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4438 pattern childGuard
    simpa only [d97, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d97, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4434 pattern childGuard
    simpa only [d97, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4440 (pattern : Twelve) (guard : d0 pattern = 1) : d6 pattern ≤ (0 : Int) + d281 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4441 (pattern : Twelve) (guard : d1857 pattern = 1) : d356 pattern ≤ (0 : Int) + d289 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d356, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4439 pattern childGuard
    simpa only [d1857, d356, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d356, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4440 pattern childGuard
    simpa only [d1857, d356, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4442 (pattern : Twelve) (guard : d1857 pattern = 1) : d356 pattern ≤ (0 : Int) + d290 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d356, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4439 pattern childGuard
    simpa only [d1857, d356, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d356, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1857, d356, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4443 (pattern : Twelve) (guard : d1857 pattern = 1) : d356 pattern ≤ (0 : Int) + d295 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4441 pattern childGuard
    simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4442 pattern childGuard
    simpa only [d295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4444 (pattern : Twelve) (guard : d1857 pattern = 1) : d356 pattern ≤ (0 : Int) + d298 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4437 pattern childGuard
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4443 pattern childGuard
    simpa only [d298, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4445 (pattern : Twelve) (guard : d1857 pattern = 1) : d362 pattern ≤ (0 : Int) + d300 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d362, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4429 pattern childGuard
    simpa only [d362, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d362, d300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4444 pattern childGuard
    simpa only [d362, d300, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4446 (pattern : Twelve) (guard : d1849 pattern = 1) : d51 pattern ≤ (0 : Int) + d255 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d51, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1830 pattern childGuard
    simpa only [d1849, d51, d255, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d51, d255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c101 pattern childGuard
    simpa only [d1849, d51, d255, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4447 (pattern : Twelve) (guard : d1849 pattern = 1) : d73 pattern ≤ (0 : Int) + d270 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d73, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4430 pattern childGuard
    simpa only [d73, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d73, d270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4446 pattern childGuard
    simpa only [d73, d270, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4448 (pattern : Twelve) (guard : d1849 pattern = 1) : d91 pattern ≤ (0 : Int) + d282 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d91, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4432 pattern childGuard
    simpa only [d91, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d91, d282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4447 pattern childGuard
    simpa only [d91, d282, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4449 (pattern : Twelve) (guard : d1857 pattern = 1) : d357 pattern ≤ (0 : Int) + d291 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d357, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4448 pattern childGuard
    simpa only [d1857, d357, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d357, d291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4436 pattern childGuard
    simpa only [d1857, d357, d291, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4450 (pattern : Twelve) (guard : d1849 pattern = 1) : d76 pattern ≤ (0 : Int) + d271 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d76, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4430 pattern childGuard
    simpa only [d76, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d76, d271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4397 pattern childGuard
    simpa only [d76, d271, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4451 (pattern : Twelve) (guard : d1849 pattern = 1) : d93 pattern ≤ (0 : Int) + d283 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d93, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4432 pattern childGuard
    simpa only [d93, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d93, d283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4450 pattern childGuard
    simpa only [d93, d283, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4452 (pattern : Twelve) (guard : d1857 pattern = 1) : d355 pattern ≤ (0 : Int) + d292 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d355, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4451 pattern childGuard
    simpa only [d1857, d355, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d355, d292, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4436 pattern childGuard
    simpa only [d1857, d355, d292, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4453 (pattern : Twelve) (guard : d1857 pattern = 1) : d360 pattern ≤ (0 : Int) + d296 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d360, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4449 pattern childGuard
    simpa only [d360, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d360, d296, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4452 pattern childGuard
    simpa only [d360, d296, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4454 (pattern : Twelve) (guard : d1849 pattern = 1) : d73 pattern ≤ (0 : Int) + d263 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d73, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4424 pattern childGuard
    simpa only [d73, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d73, d263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4415 pattern childGuard
    simpa only [d73, d263, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4455 (pattern : Twelve) (guard : d1849 pattern = 1) : d91 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d91, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4438 pattern childGuard
    simpa only [d91, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d91, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4454 pattern childGuard
    simpa only [d91, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4456 (pattern : Twelve) (guard : d1857 pattern = 1) : d357 pattern ≤ (0 : Int) + d289 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d357, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4455 pattern childGuard
    simpa only [d1857, d357, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d357, d289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4440 pattern childGuard
    simpa only [d1857, d357, d289, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4457 (pattern : Twelve) (guard : d1849 pattern = 1) : d93 pattern ≤ (0 : Int) + d280 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d93, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4438 pattern childGuard
    simpa only [d93, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d93, d280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4425 pattern childGuard
    simpa only [d93, d280, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4458 (pattern : Twelve) (guard : d1857 pattern = 1) : d355 pattern ≤ (0 : Int) + d290 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d355, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4457 pattern childGuard
    simpa only [d1857, d355, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d355, d290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1459 pattern childGuard
    simpa only [d1857, d355, d290, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4459 (pattern : Twelve) (guard : d1857 pattern = 1) : d360 pattern ≤ (0 : Int) + d295 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d360, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4456 pattern childGuard
    simpa only [d360, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d360, d295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4458 pattern childGuard
    simpa only [d360, d295, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4460 (pattern : Twelve) (guard : d1857 pattern = 1) : d360 pattern ≤ (0 : Int) + d299 pattern := by
  cases selected : pattern.c with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4453 pattern childGuard
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4459 pattern childGuard
    simpa only [d299, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4461 (pattern : Twelve) (guard : d1857 pattern = 1) : d363 pattern ≤ (0 : Int) + d301 pattern := by
  cases selected : pattern.g with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d363, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4460 pattern childGuard
    simpa only [d363, d301, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d363, d301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4444 pattern childGuard
    simpa only [d363, d301, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4462 (pattern : Twelve) (guard : d1857 pattern = 1) : d364 pattern ≤ (0 : Int) + d302 pattern := by
  cases selected : pattern.b with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d364, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4445 pattern childGuard
    simpa only [d364, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d364, d302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4461 pattern childGuard
    simpa only [d364, d302, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4463 (pattern : Twelve) (guard : d1857 pattern = 1) : d365 pattern ≤ (0 : Int) + d303 pattern := by
  cases selected : pattern.a with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d365, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4462 pattern childGuard
    simpa only [d365, d303, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d365, d303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4461 pattern childGuard
    simpa only [d365, d303, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4464 (pattern : Twelve) (guard : d1849 pattern = 1) : d824 pattern ≤ (0 : Int) + d940 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d824, d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1902 pattern childGuard
    simpa only [d1849, d824, d940, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d824, d940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c237 pattern childGuard
    simpa only [d1849, d824, d940, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4465 (pattern : Twelve) (guard : d1849 pattern = 1) : d838 pattern ≤ (0 : Int) + d947 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d838, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4387 pattern childGuard
    simpa only [d838, d947, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d838, d947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4464 pattern childGuard
    simpa only [d838, d947, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4466 (pattern : Twelve) (guard : d1849 pattern = 1) : d17 pattern ≤ (0 : Int) + d941 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1670 pattern childGuard
    simpa only [d1849, d941, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c241 pattern childGuard
    simpa only [d1849, d941, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4467 (pattern : Twelve) (guard : d1849 pattern = 1) : d825 pattern ≤ (0 : Int) + d942 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d825, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1747 pattern childGuard
    simpa only [d1849, d825, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d825, d942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c144 pattern childGuard
    simpa only [d1849, d825, d942, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4468 (pattern : Twelve) (guard : d1849 pattern = 1) : d839 pattern ≤ (0 : Int) + d948 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d839, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4466 pattern childGuard
    simpa only [d839, d948, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d839, d948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4467 pattern childGuard
    simpa only [d839, d948, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4469 (pattern : Twelve) (guard : d1849 pattern = 1) : d853 pattern ≤ (0 : Int) + d955 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d853, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4465 pattern childGuard
    simpa only [d853, d955, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d853, d955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4468 pattern childGuard
    simpa only [d853, d955, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4470 (pattern : Twelve) (guard : d0 pattern = 1) : d913 pattern ≤ (0 : Int) + d956 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4471 (pattern : Twelve) (guard : d1857 pattern = 1) : d1018 pattern ≤ (0 : Int) + d963 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1018, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4469 pattern childGuard
    simpa only [d1857, d1018, d963, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1018, d963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4470 pattern childGuard
    simpa only [d1857, d1018, d963, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4472 (pattern : Twelve) (guard : d1849 pattern = 1) : d824 pattern ≤ (0 : Int) + d943 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d824, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1902 pattern childGuard
    simpa only [d1849, d824, d943, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d824, d943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c256 pattern childGuard
    simpa only [d1849, d824, d943, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4473 (pattern : Twelve) (guard : d1849 pattern = 1) : d838 pattern ≤ (0 : Int) + d950 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d838, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4396 pattern childGuard
    simpa only [d838, d950, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d838, d950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4472 pattern childGuard
    simpa only [d838, d950, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4474 (pattern : Twelve) (guard : d1849 pattern = 1) : d17 pattern ≤ (0 : Int) + d944 pattern := by
  cases selected : pattern.h with
  | false =>
    have childGuard : d1848 pattern = 1 := by simpa only [d1849, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c1670 pattern childGuard
    simpa only [d1849, d944, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1849, d944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c259 pattern childGuard
    simpa only [d1849, d944, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4475 (pattern : Twelve) (guard : d1849 pattern = 1) : d839 pattern ≤ (0 : Int) + d951 pattern := by
  cases selected : pattern.f with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d839, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4474 pattern childGuard
    simpa only [d839, d951, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d839, d951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4467 pattern childGuard
    simpa only [d839, d951, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4476 (pattern : Twelve) (guard : d1849 pattern = 1) : d853 pattern ≤ (0 : Int) + d957 pattern := by
  cases selected : pattern.e with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d853, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4473 pattern childGuard
    simpa only [d853, d957, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1849 pattern = 1 := by simpa only [d853, d957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4475 pattern childGuard
    simpa only [d853, d957, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4477 (pattern : Twelve) (guard : d0 pattern = 1) : d914 pattern ≤ (0 : Int) + d958 pattern := by
  change (0 : Int) = 1 at guard
  omega
theorem c4478 (pattern : Twelve) (guard : d1857 pattern = 1) : d1019 pattern ≤ (0 : Int) + d964 pattern := by
  cases selected : pattern.j with
  | false =>
    have childGuard : d1849 pattern = 1 := by simpa only [d1857, d1019, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4476 pattern childGuard
    simpa only [d1857, d1019, d964, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d0 pattern = 1 := by simpa only [d1857, d1019, d964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4477 pattern childGuard
    simpa only [d1857, d1019, d964, selected, Bool.false_eq_true, ↓reduceIte] using child
theorem c4479 (pattern : Twelve) (guard : d1857 pattern = 1) : d1023 pattern ≤ (0 : Int) + d970 pattern := by
  cases selected : pattern.d with
  | false =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1023, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4471 pattern childGuard
    simpa only [d1023, d970, selected, Bool.false_eq_true, ↓reduceIte] using child
  | true =>
    have childGuard : d1857 pattern = 1 := by simpa only [d1023, d970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have child := c4478 pattern childGuard
    simpa only [d1023, d970, selected, Bool.false_eq_true, ↓reduceIte] using child
end NetHack.Sokoban21.Diagram
