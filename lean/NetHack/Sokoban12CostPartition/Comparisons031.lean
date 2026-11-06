/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban12CostPartition.Comparisons030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban12CostPartition
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4340 (p : Pattern) (guard : d1053 p = 1) : d501 p ≤ (0 : Int) + d466 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d501, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4320 p hg
    simpa only [d501, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d501, d466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4041 p hg
    simpa only [d501, d466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4341 (p : Pattern) (guard : d1053 p = 1) : d501 p ≤ (0 : Int) + d467 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4321 p hg
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4340 p hg
    simpa only [d467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4342 (p : Pattern) (guard : d1053 p = 1) : d501 p ≤ (0 : Int) + d468 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4321 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4341 p hg
    simpa only [d468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4343 (p : Pattern) (guard : d1053 p = 1) : d503 p ≤ (0 : Int) + d469 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d503, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4323 p hg
    simpa only [d503, d469, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d503, d469, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4045 p hg
    simpa only [d503, d469, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4344 (p : Pattern) (guard : d1053 p = 1) : d503 p ≤ (0 : Int) + d470 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4324 p hg
    simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4343 p hg
    simpa only [d470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4345 (p : Pattern) (guard : d1053 p = 1) : d503 p ≤ (0 : Int) + d471 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4324 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4344 p hg
    simpa only [d471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4346 (p : Pattern) (guard : d1053 p = 1) : d504 p ≤ (0 : Int) + d472 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d504, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4342 p hg
    simpa only [d504, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d504, d472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4345 p hg
    simpa only [d504, d472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4347 (p : Pattern) (guard : d1053 p = 1) : d519 p ≤ (0 : Int) + d473 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d519, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4346 p hg
    simpa only [d519, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d519, d473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4038 p hg
    simpa only [d519, d473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4348 (p : Pattern) (guard : d1053 p = 1) : d509 p ≤ (0 : Int) + d474 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d509, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4340 p hg
    simpa only [d509, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d509, d474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d509, d474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4349 (p : Pattern) (guard : d1053 p = 1) : d510 p ≤ (0 : Int) + d475 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d510, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4343 p hg
    simpa only [d510, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d510, d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d510, d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4350 (p : Pattern) (guard : d1053 p = 1) : d511 p ≤ (0 : Int) + d476 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d511, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4348 p hg
    simpa only [d511, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d511, d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4349 p hg
    simpa only [d511, d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4351 (p : Pattern) (guard : d1053 p = 1) : d520 p ≤ (0 : Int) + d477 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d520, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4350 p hg
    simpa only [d520, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d520, d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4038 p hg
    simpa only [d520, d477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4352 (p : Pattern) (guard : d1053 p = 1) : d521 p ≤ (0 : Int) + d478 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d521, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4347 p hg
    simpa only [d521, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d521, d478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4351 p hg
    simpa only [d521, d478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4353 (p : Pattern) (guard : d1053 p = 1) : d509 p ≤ (0 : Int) + d479 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d509, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4341 p hg
    simpa only [d509, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d509, d479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2527 p hg
    simpa only [d509, d479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4354 (p : Pattern) (guard : d1053 p = 1) : d510 p ≤ (0 : Int) + d480 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d510, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4344 p hg
    simpa only [d510, d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d510, d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2529 p hg
    simpa only [d510, d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4355 (p : Pattern) (guard : d1053 p = 1) : d511 p ≤ (0 : Int) + d481 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d511, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4353 p hg
    simpa only [d511, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d511, d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4354 p hg
    simpa only [d511, d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4356 (p : Pattern) (guard : d1053 p = 1) : d520 p ≤ (0 : Int) + d482 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d520, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4355 p hg
    simpa only [d520, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d520, d482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4038 p hg
    simpa only [d520, d482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4357 (p : Pattern) (guard : d1053 p = 1) : d522 p ≤ (0 : Int) + d483 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d522, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4356 p hg
    simpa only [d522, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d522, d483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4038 p hg
    simpa only [d522, d483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4358 (p : Pattern) (guard : d1053 p = 1) : d523 p ≤ (0 : Int) + d484 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d523, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4352 p hg
    simpa only [d523, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d523, d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4357 p hg
    simpa only [d523, d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4359 (p : Pattern) (guard : d1053 p = 1) : d524 p ≤ (0 : Int) + d485 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1053 p = 1 := by simpa only [d524, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4339 p hg
    simpa only [d524, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1053 p = 1 := by simpa only [d524, d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4358 p hg
    simpa only [d524, d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4360 (p : Pattern) (guard : d0 p = 1) : d119 p ≤ (2 : Int) + d7 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4361 (p : Pattern) (guard : d1158 p = 1) : d119 p ≤ (2 : Int) + d7 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4360 p hg
    simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4256 p hg
    simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4362 (p : Pattern) (guard : d851 p = 1) : d55 p ≤ (2 : Int) + d7 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare77 p hg
    simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare767 p hg
    simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4363 (p : Pattern) (guard : d1158 p = 1) : d137 p ≤ (2 : Int) + d7 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1158, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4360 p hg
    simpa only [d1158, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d1158, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4362 p hg
    simpa only [d1158, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4364 (p : Pattern) (guard : d1158 p = 1) : d501 p ≤ (2 : Int) + d7 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4361 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4363 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4365 (p : Pattern) (guard : d0 p = 1) : d125 p ≤ (2 : Int) + d11 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4366 (p : Pattern) (guard : d1158 p = 1) : d125 p ≤ (2 : Int) + d11 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4365 p hg
    simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4260 p hg
    simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4367 (p : Pattern) (guard : d1158 p = 1) : d502 p ≤ (2 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d502, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4361 p hg
    simpa only [d502, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d502, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4366 p hg
    simpa only [d502, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4368 (p : Pattern) (guard : d851 p = 1) : d60 p ≤ (2 : Int) + d11 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare88 p hg
    simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare771 p hg
    simpa only [d851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4369 (p : Pattern) (guard : d1158 p = 1) : d143 p ≤ (2 : Int) + d11 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1158, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4365 p hg
    simpa only [d1158, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d1158, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4368 p hg
    simpa only [d1158, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4370 (p : Pattern) (guard : d1158 p = 1) : d144 p ≤ (2 : Int) + d12 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d144, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4363 p hg
    simpa only [d144, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d144, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4369 p hg
    simpa only [d144, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4371 (p : Pattern) (guard : d1158 p = 1) : d503 p ≤ (2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4367 p hg
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4370 p hg
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4372 (p : Pattern) (guard : d1158 p = 1) : d504 p ≤ (2 : Int) + d13 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d504, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4364 p hg
    simpa only [d504, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d504, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4371 p hg
    simpa only [d504, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4373 (p : Pattern) (guard : d1158 p = 1) : d55 p ≤ (2 : Int) + d55 p := by
  omega
theorem compare4374 (p : Pattern) (guard : d1158 p = 1) : d505 p ≤ (2 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4361 p hg
    simpa only [d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4373 p hg
    simpa only [d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4375 (p : Pattern) (guard : d1158 p = 1) : d65 p ≤ (2 : Int) + d65 p := by
  omega
theorem compare4376 (p : Pattern) (guard : d1158 p = 1) : d506 p ≤ (2 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4367 p hg
    simpa only [d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4375 p hg
    simpa only [d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4377 (p : Pattern) (guard : d1158 p = 1) : d507 p ≤ (2 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d507, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4374 p hg
    simpa only [d507, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d507, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4376 p hg
    simpa only [d507, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4378 (p : Pattern) (guard : d1158 p = 1) : d508 p ≤ (2 : Int) + d1018 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d508, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4372 p hg
    simpa only [d508, d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d508, d1018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4377 p hg
    simpa only [d508, d1018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4379 (p : Pattern) (guard : d1158 p = 1) : d509 p ≤ (2 : Int) + d832 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d509, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4364 p hg
    simpa only [d509, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d509, d832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4373 p hg
    simpa only [d509, d832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4380 (p : Pattern) (guard : d1158 p = 1) : d510 p ≤ (2 : Int) + d833 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d510, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4371 p hg
    simpa only [d510, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d510, d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4375 p hg
    simpa only [d510, d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4381 (p : Pattern) (guard : d1158 p = 1) : d511 p ≤ (2 : Int) + d834 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d511, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4379 p hg
    simpa only [d511, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d511, d834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4380 p hg
    simpa only [d511, d834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4382 (p : Pattern) (guard : d1158 p = 1) : d512 p ≤ (2 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d512, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4374 p hg
    simpa only [d512, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d512, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4373 p hg
    simpa only [d512, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4383 (p : Pattern) (guard : d1158 p = 1) : d513 p ≤ (2 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d513, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4376 p hg
    simpa only [d513, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d513, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4375 p hg
    simpa only [d513, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4384 (p : Pattern) (guard : d1158 p = 1) : d514 p ≤ (2 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d514, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4382 p hg
    simpa only [d514, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d514, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4383 p hg
    simpa only [d514, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4385 (p : Pattern) (guard : d1158 p = 1) : d515 p ≤ (2 : Int) + d1019 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d515, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4381 p hg
    simpa only [d515, d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d515, d1019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4384 p hg
    simpa only [d515, d1019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4386 (p : Pattern) (guard : d1158 p = 1) : d516 p ≤ (2 : Int) + d1020 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d516, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4378 p hg
    simpa only [d516, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d516, d1020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4385 p hg
    simpa only [d516, d1020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4387 (p : Pattern) (guard : d1158 p = 1) : d66 p ≤ (2 : Int) + d66 p := by
  omega
theorem compare4388 (p : Pattern) (guard : d1158 p = 1) : d517 p ≤ (2 : Int) + d1021 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d517, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4385 p hg
    simpa only [d517, d1021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d517, d1021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4387 p hg
    simpa only [d517, d1021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4389 (p : Pattern) (guard : d1158 p = 1) : d518 p ≤ (2 : Int) + d1022 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d518, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4386 p hg
    simpa only [d518, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d518, d1022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4388 p hg
    simpa only [d518, d1022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4390 (p : Pattern) (guard : d0 p = 1) : d119 p ≤ (2 : Int) + d119 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4391 (p : Pattern) (guard : d851 p = 1) : d55 p ≤ (2 : Int) + d119 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare77 p hg
    simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2333 p hg
    simpa only [d851, d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4392 (p : Pattern) (guard : d1158 p = 1) : d137 p ≤ (2 : Int) + d119 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1158, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4390 p hg
    simpa only [d1158, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d1158, d137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4391 p hg
    simpa only [d1158, d137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4393 (p : Pattern) (guard : d1158 p = 1) : d501 p ≤ (2 : Int) + d1023 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d501, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4361 p hg
    simpa only [d501, d1023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d501, d1023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4392 p hg
    simpa only [d501, d1023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4394 (p : Pattern) (guard : d1158 p = 1) : d501 p ≤ (2 : Int) + d1024 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4364 p hg
    simpa only [d1024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d1024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4393 p hg
    simpa only [d1024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4395 (p : Pattern) (guard : d1158 p = 1) : d501 p ≤ (2 : Int) + d1025 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4364 p hg
    simpa only [d1025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d1025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4394 p hg
    simpa only [d1025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4396 (p : Pattern) (guard : d0 p = 1) : d125 p ≤ (2 : Int) + d125 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4397 (p : Pattern) (guard : d851 p = 1) : d60 p ≤ (2 : Int) + d125 p := by
  cases selected : p 187 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare88 p hg
    simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2737 p hg
    simpa only [d851, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4398 (p : Pattern) (guard : d1158 p = 1) : d143 p ≤ (2 : Int) + d125 p := by
  cases selected : p 186 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1158, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4396 p hg
    simpa only [d1158, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d851 p = 1 := by simpa only [d1158, d143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4397 p hg
    simpa only [d1158, d143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4399 (p : Pattern) (guard : d1158 p = 1) : d144 p ≤ (2 : Int) + d502 p := by
  cases selected : p 168 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d144, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4392 p hg
    simpa only [d144, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d144, d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4398 p hg
    simpa only [d144, d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4400 (p : Pattern) (guard : d1158 p = 1) : d503 p ≤ (2 : Int) + d1026 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d503, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4367 p hg
    simpa only [d503, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d503, d1026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d503, d1026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4401 (p : Pattern) (guard : d1158 p = 1) : d503 p ≤ (2 : Int) + d1027 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4371 p hg
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4402 (p : Pattern) (guard : d1158 p = 1) : d503 p ≤ (2 : Int) + d1028 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4371 p hg
    simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d1028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4403 (p : Pattern) (guard : d1158 p = 1) : d504 p ≤ (2 : Int) + d1029 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d504, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4395 p hg
    simpa only [d504, d1029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d504, d1029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d504, d1029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4404 (p : Pattern) (guard : d1158 p = 1) : d519 p ≤ (2 : Int) + d1030 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d519, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d519, d1030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d519, d1030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4387 p hg
    simpa only [d519, d1030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4405 (p : Pattern) (guard : d1158 p = 1) : d509 p ≤ (2 : Int) + d1031 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d509, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4393 p hg
    simpa only [d509, d1031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d509, d1031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4373 p hg
    simpa only [d509, d1031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4406 (p : Pattern) (guard : d1158 p = 1) : d510 p ≤ (2 : Int) + d1032 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d510, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d510, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d510, d1032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4375 p hg
    simpa only [d510, d1032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4407 (p : Pattern) (guard : d1158 p = 1) : d511 p ≤ (2 : Int) + d1033 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d511, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4405 p hg
    simpa only [d511, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d511, d1033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4406 p hg
    simpa only [d511, d1033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4408 (p : Pattern) (guard : d1158 p = 1) : d520 p ≤ (2 : Int) + d1034 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d520, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4407 p hg
    simpa only [d520, d1034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d520, d1034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4387 p hg
    simpa only [d520, d1034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4409 (p : Pattern) (guard : d1158 p = 1) : d521 p ≤ (2 : Int) + d1035 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d521, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d521, d1035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d521, d1035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d521, d1035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4410 (p : Pattern) (guard : d1158 p = 1) : d509 p ≤ (2 : Int) + d1036 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d509, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4394 p hg
    simpa only [d509, d1036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d509, d1036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4373 p hg
    simpa only [d509, d1036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4411 (p : Pattern) (guard : d1158 p = 1) : d510 p ≤ (2 : Int) + d1037 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d510, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d510, d1037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d510, d1037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4375 p hg
    simpa only [d510, d1037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4412 (p : Pattern) (guard : d1158 p = 1) : d511 p ≤ (2 : Int) + d1038 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d511, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4410 p hg
    simpa only [d511, d1038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d511, d1038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4411 p hg
    simpa only [d511, d1038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4413 (p : Pattern) (guard : d1158 p = 1) : d520 p ≤ (2 : Int) + d1039 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d520, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4412 p hg
    simpa only [d520, d1039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d520, d1039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4387 p hg
    simpa only [d520, d1039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4414 (p : Pattern) (guard : d1158 p = 1) : d522 p ≤ (2 : Int) + d1040 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d522, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4413 p hg
    simpa only [d522, d1040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d522, d1040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4387 p hg
    simpa only [d522, d1040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4415 (p : Pattern) (guard : d1158 p = 1) : d523 p ≤ (2 : Int) + d1041 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d523, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4409 p hg
    simpa only [d523, d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d523, d1041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4414 p hg
    simpa only [d523, d1041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4416 (p : Pattern) (guard : d1158 p = 1) : d524 p ≤ (2 : Int) + d1042 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d524, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4389 p hg
    simpa only [d524, d1042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1158 p = 1 := by simpa only [d524, d1042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4415 p hg
    simpa only [d524, d1042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4417 (p : Pattern) (guard : d1047 p = 1) : d501 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d1047, d501, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4080 p hg
    simpa only [d1047, d501, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1047, d501, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1866 p hg
    simpa only [d1047, d501, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4418 (p : Pattern) (guard : d1047 p = 1) : d503 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d1047, d503, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4148 p hg
    simpa only [d1047, d503, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1047, d503, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1870 p hg
    simpa only [d1047, d503, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4419 (p : Pattern) (guard : d1047 p = 1) : d504 p ≤ (0 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d504, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4417 p hg
    simpa only [d504, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d504, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4418 p hg
    simpa only [d504, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4420 (p : Pattern) (guard : d1047 p = 1) : d505 p ≤ (0 : Int) + d106 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d1047, d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4080 p hg
    simpa only [d1047, d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1047, d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare728 p hg
    simpa only [d1047, d505, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4421 (p : Pattern) (guard : d1047 p = 1) : d506 p ≤ (0 : Int) + d109 p := by
  cases selected : p 160 with
  | false =>
    have hg : d851 p = 1 := by simpa only [d1047, d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4148 p hg
    simpa only [d1047, d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1047, d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare732 p hg
    simpa only [d1047, d506, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4422 (p : Pattern) (guard : d1047 p = 1) : d507 p ≤ (0 : Int) + d227 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d507, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d507, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d507, d227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4421 p hg
    simpa only [d507, d227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4423 (p : Pattern) (guard : d1047 p = 1) : d508 p ≤ (0 : Int) + d227 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4419 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4422 p hg
    simpa only [d508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4424 (p : Pattern) (guard : d1047 p = 1) : d509 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d509, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4417 p hg
    simpa only [d509, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d509, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2378 p hg
    simpa only [d509, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4425 (p : Pattern) (guard : d1047 p = 1) : d510 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d510, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4418 p hg
    simpa only [d510, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d510, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2380 p hg
    simpa only [d510, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4426 (p : Pattern) (guard : d1047 p = 1) : d511 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d511, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d511, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d511, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4425 p hg
    simpa only [d511, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4427 (p : Pattern) (guard : d1047 p = 1) : d512 p ≤ (0 : Int) + d229 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d512, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d512, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d512, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2378 p hg
    simpa only [d512, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4428 (p : Pattern) (guard : d1047 p = 1) : d513 p ≤ (0 : Int) + d230 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d513, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4421 p hg
    simpa only [d513, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d513, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2380 p hg
    simpa only [d513, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4429 (p : Pattern) (guard : d1047 p = 1) : d514 p ≤ (0 : Int) + d231 p := by
  cases selected : p 141 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d514, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4427 p hg
    simpa only [d514, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d514, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4428 p hg
    simpa only [d514, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4430 (p : Pattern) (guard : d1047 p = 1) : d515 p ≤ (0 : Int) + d231 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4429 p hg
    simpa only [d515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4431 (p : Pattern) (guard : d1047 p = 1) : d516 p ≤ (0 : Int) + d366 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d516, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4423 p hg
    simpa only [d516, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d516, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4430 p hg
    simpa only [d516, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4432 (p : Pattern) (guard : d1047 p = 1) : d517 p ≤ (0 : Int) + d367 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d517, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4430 p hg
    simpa only [d517, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d517, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2388 p hg
    simpa only [d517, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4433 (p : Pattern) (guard : d1047 p = 1) : d518 p ≤ (0 : Int) + d368 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d518, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4431 p hg
    simpa only [d518, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d518, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d518, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4434 (p : Pattern) (guard : d1047 p = 1) : d519 p ≤ (0 : Int) + d369 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d519, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4419 p hg
    simpa only [d519, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d519, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2388 p hg
    simpa only [d519, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4435 (p : Pattern) (guard : d1047 p = 1) : d520 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d520, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d520, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d520, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2388 p hg
    simpa only [d520, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4436 (p : Pattern) (guard : d1047 p = 1) : d521 p ≤ (0 : Int) + d371 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d521, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4434 p hg
    simpa only [d521, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d521, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4435 p hg
    simpa only [d521, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4437 (p : Pattern) (guard : d1047 p = 1) : d522 p ≤ (0 : Int) + d372 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d522, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4435 p hg
    simpa only [d522, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d522, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2388 p hg
    simpa only [d522, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4438 (p : Pattern) (guard : d1047 p = 1) : d523 p ≤ (0 : Int) + d373 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d523, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d523, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d523, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4437 p hg
    simpa only [d523, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4439 (p : Pattern) (guard : d1047 p = 1) : d524 p ≤ (0 : Int) + d374 p := by
  cases selected : p 108 with
  | false =>
    have hg : d1047 p = 1 := by simpa only [d524, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4433 p hg
    simpa only [d524, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1047 p = 1 := by simpa only [d524, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4438 p hg
    simpa only [d524, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4440 (p : Pattern) (guard : d1 p = 1) : d258 p ≤ (8 : Int) + d258 p := by
  omega
theorem compare4441 (p : Pattern) (guard : d1 p = 1) : d258 p ≤ (5 : Int) + d258 p := by
  omega
theorem compare4442 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d6 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2641 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4443 (p : Pattern) (guard : d0 p = 1) : d6 p ≤ (2 : Int) + d6 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4444 (p : Pattern) (guard : d854 p = 1) : d7 p ≤ (2 : Int) + d6 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4442 p hg
    simpa only [d854, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4443 p hg
    simpa only [d854, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4445 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d54 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2645 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4446 (p : Pattern) (guard : d0 p = 1) : d54 p ≤ (2 : Int) + d54 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4447 (p : Pattern) (guard : d854 p = 1) : d55 p ≤ (2 : Int) + d54 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4445 p hg
    simpa only [d854, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4446 p hg
    simpa only [d854, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4448 (p : Pattern) (guard : d854 p = 1) : d56 p ≤ (2 : Int) + d855 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d56, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d56, d855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d56, d855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d56, d855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4449 (p : Pattern) (guard : d854 p = 1) : d57 p ≤ (2 : Int) + d856 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d57, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d57, d856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d57, d856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4448 p hg
    simpa only [d57, d856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4450 (p : Pattern) (guard : d1 p = 1) : d8 p ≤ (2 : Int) + d10 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2651 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4451 (p : Pattern) (guard : d0 p = 1) : d10 p ≤ (2 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4452 (p : Pattern) (guard : d854 p = 1) : d11 p ≤ (2 : Int) + d10 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4450 p hg
    simpa only [d854, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4451 p hg
    simpa only [d854, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4453 (p : Pattern) (guard : d854 p = 1) : d12 p ≤ (2 : Int) + d857 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d12, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d12, d857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d12, d857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4452 p hg
    simpa only [d12, d857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4454 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (2 : Int) + d59 p := by
  cases selected : p 193 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2656 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4455 (p : Pattern) (guard : d0 p = 1) : d59 p ≤ (2 : Int) + d59 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4456 (p : Pattern) (guard : d854 p = 1) : d60 p ≤ (2 : Int) + d59 p := by
  cases selected : p 192 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d854, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4454 p hg
    simpa only [d854, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d854, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4455 p hg
    simpa only [d854, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4457 (p : Pattern) (guard : d854 p = 1) : d61 p ≤ (2 : Int) + d858 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d61, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4452 p hg
    simpa only [d61, d858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d61, d858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4456 p hg
    simpa only [d61, d858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4458 (p : Pattern) (guard : d854 p = 1) : d62 p ≤ (2 : Int) + d859 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d62, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4448 p hg
    simpa only [d62, d859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d62, d859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4457 p hg
    simpa only [d62, d859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4459 (p : Pattern) (guard : d854 p = 1) : d63 p ≤ (2 : Int) + d860 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d63, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4453 p hg
    simpa only [d63, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d63, d860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4458 p hg
    simpa only [d63, d860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4460 (p : Pattern) (guard : d854 p = 1) : d64 p ≤ (2 : Int) + d861 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d64, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4449 p hg
    simpa only [d64, d861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d64, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4459 p hg
    simpa only [d64, d861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4461 (p : Pattern) (guard : d854 p = 1) : d106 p ≤ (2 : Int) + d862 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d106, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d106, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d106, d862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d106, d862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4462 (p : Pattern) (guard : d854 p = 1) : d119 p ≤ (2 : Int) + d863 p := by
  cases selected : p 187 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d119, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d119, d863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d119, d863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d119, d863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4463 (p : Pattern) (guard : d854 p = 1) : d120 p ≤ (2 : Int) + d864 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d120, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d120, d864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d120, d864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d120, d864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4464 (p : Pattern) (guard : d854 p = 1) : d121 p ≤ (2 : Int) + d865 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d121, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d121, d865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d121, d865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d121, d865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4465 (p : Pattern) (guard : d854 p = 1) : d122 p ≤ (2 : Int) + d866 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d122, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d122, d866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d122, d866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d122, d866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4466 (p : Pattern) (guard : d854 p = 1) : d179 p ≤ (2 : Int) + d867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d179, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d179, d867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d179, d867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d179, d867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4467 (p : Pattern) (guard : d854 p = 1) : d65 p ≤ (2 : Int) + d868 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d65, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d65, d868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d65, d868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4456 p hg
    simpa only [d65, d868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4468 (p : Pattern) (guard : d854 p = 1) : d109 p ≤ (2 : Int) + d869 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d109, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4453 p hg
    simpa only [d109, d869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d109, d869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4467 p hg
    simpa only [d109, d869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4469 (p : Pattern) (guard : d854 p = 1) : d125 p ≤ (2 : Int) + d870 p := by
  cases selected : p 187 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d125, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4452 p hg
    simpa only [d125, d870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d125, d870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4456 p hg
    simpa only [d125, d870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4470 (p : Pattern) (guard : d854 p = 1) : d126 p ≤ (2 : Int) + d871 p := by
  cases selected : p 186 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d126, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4452 p hg
    simpa only [d126, d871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d126, d871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d126, d871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4471 (p : Pattern) (guard : d854 p = 1) : d127 p ≤ (2 : Int) + d872 p := by
  cases selected : p 168 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d127, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d127, d872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d127, d872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4470 p hg
    simpa only [d127, d872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4472 (p : Pattern) (guard : d854 p = 1) : d128 p ≤ (2 : Int) + d873 p := by
  cases selected : p 160 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d128, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4471 p hg
    simpa only [d128, d873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d128, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4467 p hg
    simpa only [d128, d873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4473 (p : Pattern) (guard : d854 p = 1) : d129 p ≤ (2 : Int) + d874 p := by
  cases selected : p 159 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d129, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4468 p hg
    simpa only [d129, d874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d129, d874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4472 p hg
    simpa only [d129, d874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4474 (p : Pattern) (guard : d854 p = 1) : d237 p ≤ (2 : Int) + d875 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d237, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4468 p hg
    simpa only [d237, d875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d237, d875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d237, d875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4475 (p : Pattern) (guard : d854 p = 1) : d238 p ≤ (2 : Int) + d876 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d238, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4466 p hg
    simpa only [d238, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d238, d876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4474 p hg
    simpa only [d238, d876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4476 (p : Pattern) (guard : d854 p = 1) : d239 p ≤ (2 : Int) + d877 p := by
  cases selected : p 134 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d239, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d239, d877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d239, d877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4475 p hg
    simpa only [d239, d877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4477 (p : Pattern) (guard : d854 p = 1) : d68 p ≤ (2 : Int) + d878 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d68, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4449 p hg
    simpa only [d68, d878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d68, d878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d68, d878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4478 (p : Pattern) (guard : d854 p = 1) : d69 p ≤ (2 : Int) + d879 p := by
  cases selected : p 158 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d69, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4459 p hg
    simpa only [d69, d879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d69, d879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4467 p hg
    simpa only [d69, d879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4479 (p : Pattern) (guard : d854 p = 1) : d70 p ≤ (2 : Int) + d880 p := by
  cases selected : p 141 with
  | false =>
    have hg : d854 p = 1 := by simpa only [d70, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d70, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d854 p = 1 := by simpa only [d70, d880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4478 p hg
    simpa only [d70, d880, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban12CostPartition
