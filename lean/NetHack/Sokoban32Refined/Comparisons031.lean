/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons030
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare4340 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (2 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4341 (p : Pattern) (guard : d1 p = 1) : d58 p ≤ (2 : Int) + d61 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d58, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d58, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d58, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d58, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4342 (p : Pattern) (guard : d1 p = 1) : d59 p ≤ (2 : Int) + d62 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d59, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4323 p hg
    simpa only [d59, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d59, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4341 p hg
    simpa only [d59, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4343 (p : Pattern) (guard : d914 p = 1) : d60 p ≤ (2 : Int) + d62 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d914, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4340 p hg
    simpa only [d914, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d914, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4342 p hg
    simpa only [d914, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4344 (p : Pattern) (guard : d0 p = 1) : d63 p ≤ (2 : Int) + d62 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4345 (p : Pattern) (guard : d1175 p = 1) : d64 p ≤ (2 : Int) + d62 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4343 p hg
    simpa only [d1175, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4344 p hg
    simpa only [d1175, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4346 (p : Pattern) (guard : d1175 p = 1) : d65 p ≤ (2 : Int) + d1257 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d65, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4339 p hg
    simpa only [d65, d1257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d65, d1257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4345 p hg
    simpa only [d65, d1257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4347 (p : Pattern) (guard : d1175 p = 1) : d66 p ≤ (2 : Int) + d1258 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d66, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4336 p hg
    simpa only [d66, d1258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d66, d1258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4346 p hg
    simpa only [d66, d1258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4348 (p : Pattern) (guard : d1175 p = 1) : d67 p ≤ (2 : Int) + d1259 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d67, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4328 p hg
    simpa only [d67, d1259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d67, d1259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4347 p hg
    simpa only [d67, d1259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4349 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (2 : Int) + d69 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4350 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d1 p := by
  change (0 : Int) ≤ (2 : Int) + 1
  decide
theorem compare4351 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d9 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4350 p hg
    simpa only [d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d3, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4352 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d10 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4350 p hg
    simpa only [d4, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4351 p hg
    simpa only [d4, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4353 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d1 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4350 p hg
    simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4317 p hg
    simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4354 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (2 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4353 p hg
    simpa only [d17, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d17, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4355 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4352 p hg
    simpa only [d18, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4354 p hg
    simpa only [d18, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4356 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (2 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4354 p hg
    simpa only [d19, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d19, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4357 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (2 : Int) + d40 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4355 p hg
    simpa only [d20, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4356 p hg
    simpa only [d20, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4358 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (2 : Int) + d2 p := by
  change (1 : Int) ≤ (2 : Int) + 2
  decide
theorem compare4359 (p : Pattern) (guard : d1 p = 1) : d9 p ≤ (2 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4358 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4360 (p : Pattern) (guard : d1 p = 1) : d10 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4358 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4359 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4361 (p : Pattern) (guard : d1 p = 1) : d21 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4359 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4362 (p : Pattern) (guard : d1 p = 1) : d22 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4360 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4361 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4363 (p : Pattern) (guard : d1 p = 1) : d23 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4361 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4364 (p : Pattern) (guard : d1 p = 1) : d24 p ≤ (2 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4362 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4363 p hg
    simpa only [d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4365 (p : Pattern) (guard : d1 p = 1) : d25 p ≤ (2 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d25, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4357 p hg
    simpa only [d25, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d25, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4364 p hg
    simpa only [d25, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4366 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (2 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4357 p hg
    simpa only [d26, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4365 p hg
    simpa only [d26, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4367 (p : Pattern) (guard : d914 p = 1) : d27 p ≤ (2 : Int) + d69 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d914, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4349 p hg
    simpa only [d914, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d914, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4366 p hg
    simpa only [d914, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4368 (p : Pattern) (guard : d0 p = 1) : d72 p ≤ (2 : Int) + d69 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4369 (p : Pattern) (guard : d1175 p = 1) : d73 p ≤ (2 : Int) + d69 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4367 p hg
    simpa only [d1175, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4368 p hg
    simpa only [d1175, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4370 (p : Pattern) (guard : d1175 p = 1) : d74 p ≤ (2 : Int) + d1260 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d74, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4304 p hg
    simpa only [d74, d1260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d74, d1260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4369 p hg
    simpa only [d74, d1260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4371 (p : Pattern) (guard : d0 p = 1) : d16 p ≤ (2 : Int) + d68 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4372 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) ≤ (2 : Int) + 2
  decide
theorem compare4373 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4372 p hg
    simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4374 (p : Pattern) (guard : d1 p = 1) : d4 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4372 p hg
    simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4373 p hg
    simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4375 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4373 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4376 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4374 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4375 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4377 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4375 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4378 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (2 : Int) + d2 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4376 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4377 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4379 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (2 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4357 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4378 p hg
    simpa only [d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4380 (p : Pattern) (guard : d1 p = 1) : d26 p ≤ (2 : Int) + d68 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4379 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4365 p hg
    simpa only [d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4381 (p : Pattern) (guard : d914 p = 1) : d27 p ≤ (2 : Int) + d68 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d914, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4371 p hg
    simpa only [d914, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d914, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4380 p hg
    simpa only [d914, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4382 (p : Pattern) (guard : d0 p = 1) : d75 p ≤ (2 : Int) + d68 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4383 (p : Pattern) (guard : d1175 p = 1) : d76 p ≤ (2 : Int) + d68 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4381 p hg
    simpa only [d1175, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4382 p hg
    simpa only [d1175, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4384 (p : Pattern) (guard : d1175 p = 1) : d77 p ≤ (2 : Int) + d1261 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d77, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4304 p hg
    simpa only [d77, d1261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d77, d1261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4383 p hg
    simpa only [d77, d1261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4385 (p : Pattern) (guard : d1175 p = 1) : d78 p ≤ (2 : Int) + d1262 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d78, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4370 p hg
    simpa only [d78, d1262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d78, d1262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4384 p hg
    simpa only [d78, d1262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4386 (p : Pattern) (guard : d0 p = 1) : d15 p ≤ (2 : Int) + d68 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4387 (p : Pattern) (guard : d914 p = 1) : d46 p ≤ (2 : Int) + d68 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d914, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4386 p hg
    simpa only [d914, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d914, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4365 p hg
    simpa only [d914, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4388 (p : Pattern) (guard : d1175 p = 1) : d79 p ≤ (2 : Int) + d68 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4387 p hg
    simpa only [d1175, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4382 p hg
    simpa only [d1175, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4389 (p : Pattern) (guard : d1175 p = 1) : d80 p ≤ (2 : Int) + d1263 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d80, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4331 p hg
    simpa only [d80, d1263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d80, d1263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4388 p hg
    simpa only [d80, d1263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4390 (p : Pattern) (guard : d0 p = 1) : d53 p ≤ (2 : Int) + d68 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4391 (p : Pattern) (guard : d1 p = 1) : d54 p ≤ (2 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d54, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4357 p hg
    simpa only [d54, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d54, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d54, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4392 (p : Pattern) (guard : d1 p = 1) : d55 p ≤ (2 : Int) + d68 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4365 p hg
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4391 p hg
    simpa only [d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4393 (p : Pattern) (guard : d914 p = 1) : d56 p ≤ (2 : Int) + d68 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d914, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4390 p hg
    simpa only [d914, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d914, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4392 p hg
    simpa only [d914, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4394 (p : Pattern) (guard : d1175 p = 1) : d81 p ≤ (2 : Int) + d68 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4393 p hg
    simpa only [d1175, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4382 p hg
    simpa only [d1175, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4395 (p : Pattern) (guard : d1175 p = 1) : d82 p ≤ (2 : Int) + d1264 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d82, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4339 p hg
    simpa only [d82, d1264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d82, d1264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4394 p hg
    simpa only [d82, d1264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4396 (p : Pattern) (guard : d1175 p = 1) : d83 p ≤ (2 : Int) + d1265 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d83, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4389 p hg
    simpa only [d83, d1265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d83, d1265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4395 p hg
    simpa only [d83, d1265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4397 (p : Pattern) (guard : d1175 p = 1) : d84 p ≤ (2 : Int) + d1266 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d84, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4385 p hg
    simpa only [d84, d1266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d84, d1266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4396 p hg
    simpa only [d84, d1266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4398 (p : Pattern) (guard : d1175 p = 1) : d85 p ≤ (2 : Int) + d1267 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d85, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4348 p hg
    simpa only [d85, d1267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d85, d1267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4397 p hg
    simpa only [d85, d1267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4399 (p : Pattern) (guard : d914 p = 1) : d86 p ≤ (2 : Int) + d86 p := by
  omega
theorem compare4400 (p : Pattern) (guard : d0 p = 1) : d88 p ≤ (2 : Int) + d86 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4401 (p : Pattern) (guard : d1175 p = 1) : d89 p ≤ (2 : Int) + d86 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d1175, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1175, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4402 (p : Pattern) (guard : d0 p = 1) : d86 p ≤ (2 : Int) + d92 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4403 (p : Pattern) (guard : d1 p = 1) : d90 p ≤ (2 : Int) + d92 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d90, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d90, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d90, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4341 p hg
    simpa only [d90, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4404 (p : Pattern) (guard : d914 p = 1) : d91 p ≤ (2 : Int) + d92 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d914, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d914, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d914, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d914, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4405 (p : Pattern) (guard : d0 p = 1) : d93 p ≤ (2 : Int) + d92 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4406 (p : Pattern) (guard : d1175 p = 1) : d94 p ≤ (2 : Int) + d92 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d1175, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4405 p hg
    simpa only [d1175, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4407 (p : Pattern) (guard : d1175 p = 1) : d95 p ≤ (2 : Int) + d1268 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d95, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d95, d1268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d95, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4406 p hg
    simpa only [d95, d1268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4408 (p : Pattern) (guard : d1175 p = 1) : d96 p ≤ (2 : Int) + d1269 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d96, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4328 p hg
    simpa only [d96, d1269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d96, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4407 p hg
    simpa only [d96, d1269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4409 (p : Pattern) (guard : d914 p = 1) : d98 p ≤ (2 : Int) + d98 p := by
  omega
theorem compare4410 (p : Pattern) (guard : d0 p = 1) : d99 p ≤ (2 : Int) + d98 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4411 (p : Pattern) (guard : d1175 p = 1) : d100 p ≤ (2 : Int) + d98 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4409 p hg
    simpa only [d1175, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4410 p hg
    simpa only [d1175, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4412 (p : Pattern) (guard : d0 p = 1) : d98 p ≤ (2 : Int) + d69 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4413 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (2 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4322 p hg
    simpa only [d70, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d70, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4414 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (2 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4322 p hg
    simpa only [d71, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4413 p hg
    simpa only [d71, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4415 (p : Pattern) (guard : d914 p = 1) : d99 p ≤ (2 : Int) + d69 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d914, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4412 p hg
    simpa only [d914, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d914, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4414 p hg
    simpa only [d914, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4416 (p : Pattern) (guard : d1175 p = 1) : d101 p ≤ (2 : Int) + d69 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4415 p hg
    simpa only [d1175, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4368 p hg
    simpa only [d1175, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4417 (p : Pattern) (guard : d1175 p = 1) : d102 p ≤ (2 : Int) + d1270 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d102, d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4411 p hg
    simpa only [d102, d1270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d102, d1270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d102, d1270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4418 (p : Pattern) (guard : d1175 p = 1) : d103 p ≤ (2 : Int) + d1271 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d103, d1271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d103, d1271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d103, d1271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4417 p hg
    simpa only [d103, d1271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4419 (p : Pattern) (guard : d0 p = 1) : d86 p ≤ (2 : Int) + d68 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4420 (p : Pattern) (guard : d1 p = 1) : d87 p ≤ (2 : Int) + d68 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4379 p hg
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4391 p hg
    simpa only [d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4421 (p : Pattern) (guard : d914 p = 1) : d88 p ≤ (2 : Int) + d68 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d914, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4419 p hg
    simpa only [d914, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d914, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d914, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4422 (p : Pattern) (guard : d1175 p = 1) : d104 p ≤ (2 : Int) + d68 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4421 p hg
    simpa only [d1175, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4382 p hg
    simpa only [d1175, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4423 (p : Pattern) (guard : d1175 p = 1) : d105 p ≤ (2 : Int) + d1272 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d105, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d105, d1272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d105, d1272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4422 p hg
    simpa only [d105, d1272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4424 (p : Pattern) (guard : d1175 p = 1) : d106 p ≤ (2 : Int) + d1273 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d106, d1273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4384 p hg
    simpa only [d106, d1273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d106, d1273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4423 p hg
    simpa only [d106, d1273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4425 (p : Pattern) (guard : d0 p = 1) : d98 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4426 (p : Pattern) (guard : d1 p = 1) : d70 p ≤ (2 : Int) + d2 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4364 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4427 (p : Pattern) (guard : d1 p = 1) : d71 p ≤ (2 : Int) + d2 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4364 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4428 (p : Pattern) (guard : d914 p = 1) : d99 p ≤ (2 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d914, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4425 p hg
    simpa only [d914, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d914, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4427 p hg
    simpa only [d914, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4429 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4430 (p : Pattern) (guard : d1175 p = 1) : d107 p ≤ (2 : Int) + d2 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4428 p hg
    simpa only [d1175, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4429 p hg
    simpa only [d1175, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4431 (p : Pattern) (guard : d1175 p = 1) : d108 p ≤ (2 : Int) + d1274 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d108, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4411 p hg
    simpa only [d108, d1274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d108, d1274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4430 p hg
    simpa only [d108, d1274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4432 (p : Pattern) (guard : d914 p = 1) : d97 p ≤ (2 : Int) + d97 p := by
  omega
theorem compare4433 (p : Pattern) (guard : d0 p = 1) : d109 p ≤ (2 : Int) + d97 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4434 (p : Pattern) (guard : d1175 p = 1) : d110 p ≤ (2 : Int) + d97 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d1175, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4433 p hg
    simpa only [d1175, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4435 (p : Pattern) (guard : d0 p = 1) : d97 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4436 (p : Pattern) (guard : d914 p = 1) : d109 p ≤ (2 : Int) + d2 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d914, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4435 p hg
    simpa only [d914, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d914, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d914, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4437 (p : Pattern) (guard : d1175 p = 1) : d111 p ≤ (2 : Int) + d2 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d1175, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4429 p hg
    simpa only [d1175, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4438 (p : Pattern) (guard : d1175 p = 1) : d112 p ≤ (2 : Int) + d1275 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d112, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4434 p hg
    simpa only [d112, d1275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d112, d1275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4437 p hg
    simpa only [d112, d1275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4439 (p : Pattern) (guard : d1175 p = 1) : d113 p ≤ (2 : Int) + d1276 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d113, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4431 p hg
    simpa only [d113, d1276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d113, d1276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4438 p hg
    simpa only [d113, d1276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4440 (p : Pattern) (guard : d1175 p = 1) : d114 p ≤ (2 : Int) + d1277 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d114, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d114, d1277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d114, d1277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4439 p hg
    simpa only [d114, d1277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4441 (p : Pattern) (guard : d1175 p = 1) : d115 p ≤ (2 : Int) + d1278 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d115, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4418 p hg
    simpa only [d115, d1278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d115, d1278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4440 p hg
    simpa only [d115, d1278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4442 (p : Pattern) (guard : d1175 p = 1) : d116 p ≤ (2 : Int) + d1279 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d116, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4398 p hg
    simpa only [d116, d1279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d116, d1279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4441 p hg
    simpa only [d116, d1279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4443 (p : Pattern) (guard : d1175 p = 1) : d117 p ≤ (2 : Int) + d1280 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d117, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4384 p hg
    simpa only [d117, d1280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d117, d1280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4396 p hg
    simpa only [d117, d1280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4444 (p : Pattern) (guard : d1175 p = 1) : d118 p ≤ (2 : Int) + d1281 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d118, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4348 p hg
    simpa only [d118, d1281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d118, d1281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4443 p hg
    simpa only [d118, d1281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4445 (p : Pattern) (guard : d1 p = 1) : d2 p ≤ (2 : Int) + d0 p := by
  change (2 : Int) ≤ (2 : Int) + 0
  decide
theorem compare4446 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (2 : Int) + d0 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4307 p hg
    simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4445 p hg
    simpa only [d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4447 (p : Pattern) (guard : d1 p = 1) : d17 p ≤ (2 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d17, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4446 p hg
    simpa only [d17, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d17, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d17, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4448 (p : Pattern) (guard : d1 p = 1) : d18 p ≤ (2 : Int) + d6 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d18, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4306 p hg
    simpa only [d18, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d18, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d18, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4449 (p : Pattern) (guard : d1 p = 1) : d19 p ≤ (2 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d19, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4447 p hg
    simpa only [d19, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d19, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d19, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4450 (p : Pattern) (guard : d1 p = 1) : d20 p ≤ (2 : Int) + d38 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d20, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4448 p hg
    simpa only [d20, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d20, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4449 p hg
    simpa only [d20, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4451 (p : Pattern) (guard : d1 p = 1) : d119 p ≤ (2 : Int) + d38 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4314 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4450 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4452 (p : Pattern) (guard : d1 p = 1) : d120 p ≤ (2 : Int) + d92 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d120, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4451 p hg
    simpa only [d120, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d120, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4341 p hg
    simpa only [d120, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4453 (p : Pattern) (guard : d914 p = 1) : d121 p ≤ (2 : Int) + d92 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d914, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d914, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d914, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4452 p hg
    simpa only [d914, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4454 (p : Pattern) (guard : d1175 p = 1) : d122 p ≤ (2 : Int) + d92 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4453 p hg
    simpa only [d1175, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4405 p hg
    simpa only [d1175, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4455 (p : Pattern) (guard : d1175 p = 1) : d123 p ≤ (2 : Int) + d1268 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d123, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d123, d1268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d123, d1268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4454 p hg
    simpa only [d123, d1268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4456 (p : Pattern) (guard : d1175 p = 1) : d124 p ≤ (2 : Int) + d1269 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d124, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4328 p hg
    simpa only [d124, d1269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d124, d1269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4455 p hg
    simpa only [d124, d1269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4457 (p : Pattern) (guard : d0 p = 1) : d97 p ≤ (2 : Int) + d68 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare4458 (p : Pattern) (guard : d914 p = 1) : d109 p ≤ (2 : Int) + d68 p := by
  cases selected : p 134 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d914, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4457 p hg
    simpa only [d914, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d914, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4413 p hg
    simpa only [d914, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4459 (p : Pattern) (guard : d1175 p = 1) : d125 p ≤ (2 : Int) + d68 p := by
  cases selected : p 133 with
  | false =>
    have hg : d914 p = 1 := by simpa only [d1175, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4458 p hg
    simpa only [d1175, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4382 p hg
    simpa only [d1175, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4460 (p : Pattern) (guard : d1175 p = 1) : d126 p ≤ (2 : Int) + d1282 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d126, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4434 p hg
    simpa only [d126, d1282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d126, d1282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4459 p hg
    simpa only [d126, d1282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4461 (p : Pattern) (guard : d1175 p = 1) : d127 p ≤ (2 : Int) + d1283 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d127, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4417 p hg
    simpa only [d127, d1283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d127, d1283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d127, d1283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4462 (p : Pattern) (guard : d1175 p = 1) : d128 p ≤ (2 : Int) + d1284 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d128, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4456 p hg
    simpa only [d128, d1284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d128, d1284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d128, d1284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4463 (p : Pattern) (guard : d1175 p = 1) : d129 p ≤ (2 : Int) + d1285 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d129, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4384 p hg
    simpa only [d129, d1285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d129, d1285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4395 p hg
    simpa only [d129, d1285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4464 (p : Pattern) (guard : d1175 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  omega
theorem compare4465 (p : Pattern) (guard : d1175 p = 1) : d130 p ≤ (2 : Int) + d1286 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d130, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4438 p hg
    simpa only [d130, d1286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d130, d1286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4464 p hg
    simpa only [d130, d1286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4466 (p : Pattern) (guard : d1175 p = 1) : d131 p ≤ (2 : Int) + d1287 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d131, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4463 p hg
    simpa only [d131, d1287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d131, d1287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4465 p hg
    simpa only [d131, d1287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4467 (p : Pattern) (guard : d1175 p = 1) : d132 p ≤ (2 : Int) + d1288 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d132, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4462 p hg
    simpa only [d132, d1288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d132, d1288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4466 p hg
    simpa only [d132, d1288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4468 (p : Pattern) (guard : d1175 p = 1) : d133 p ≤ (2 : Int) + d1289 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d133, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4444 p hg
    simpa only [d133, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d133, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4467 p hg
    simpa only [d133, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4469 (p : Pattern) (guard : d1175 p = 1) : d134 p ≤ (2 : Int) + d1290 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1175 p = 1 := by simpa only [d134, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4442 p hg
    simpa only [d134, d1290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d134, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4468 p hg
    simpa only [d134, d1290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4470 (p : Pattern) (guard : d1293 p = 1) : d4 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1213 p hg
    simpa only [d1293, d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d1293, d4, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4471 (p : Pattern) (guard : d1293 p = 1) : d5 p ≤ (0 : Int) + d5 p := by
  omega
theorem compare4472 (p : Pattern) (guard : d1293 p = 1) : d6 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4470 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4471 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4473 (p : Pattern) (guard : d1293 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare4474 (p : Pattern) (guard : d1293 p = 1) : d7 p ≤ (0 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4470 p hg
    simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d7, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4475 (p : Pattern) (guard : d1293 p = 1) : d8 p ≤ (0 : Int) + d697 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4472 p hg
    simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4474 p hg
    simpa only [d8, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4476 (p : Pattern) (guard : d1293 p = 1) : d10 p ≤ (0 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1221 p hg
    simpa only [d1293, d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d1293, d10, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4477 (p : Pattern) (guard : d1293 p = 1) : d11 p ≤ (0 : Int) + d11 p := by
  omega
theorem compare4478 (p : Pattern) (guard : d1293 p = 1) : d12 p ≤ (0 : Int) + d11 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4476 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare4479 (p : Pattern) (guard : d1293 p = 1) : d13 p ≤ (0 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4476 p hg
    simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d13, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
