import NetHack.Soko22Hazard87.Compare020
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5250 (p : Pattern) (guard : d5408 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d5407 p = 1 := by simpa only [d5408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5249 p hg
    simpa only [d5408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d5408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5251 (p : Pattern) (guard : d82073 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82072 p = 1 := by simpa only [d82073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5240 p hg
    simpa only [d82073, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5408 p = 1 := by simpa only [d82073, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5250 p hg
    simpa only [d82073, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5252 (p : Pattern) (guard : d82081 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d82081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82073 p = 1 := by simpa only [d82081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5251 p hg
    simpa only [d82081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5253 (p : Pattern) (guard : d82082 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d82082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82081 p = 1 := by simpa only [d82082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5252 p hg
    simpa only [d82082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5254 (p : Pattern) (guard : d82083 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82083, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82083, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82082 p = 1 := by simpa only [d82083, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5253 p hg
    simpa only [d82083, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5255 (p : Pattern) (guard : d82084 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d82084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82083 p = 1 := by simpa only [d82084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5254 p hg
    simpa only [d82084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5256 (p : Pattern) (guard : d488 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5234 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5257 (p : Pattern) (guard : d489 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5256 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5258 (p : Pattern) (guard : d490 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5257 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5259 (p : Pattern) (guard : d501 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d490 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5258 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5260 (p : Pattern) (guard : d639 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d501 p = 1 := by simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5259 p hg
    simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5261 (p : Pattern) (guard : d640 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d639 p = 1 := by simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5260 p hg
    simpa only [d640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5262 (p : Pattern) (guard : d641 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d640 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5261 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5263 (p : Pattern) (guard : d642 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d641 p = 1 := by simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5262 p hg
    simpa only [d642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5264 (p : Pattern) (guard : d643 p = 1) : d47766 p ≤ (-1 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4461 p hg
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d642 p = 1 := by simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5263 p hg
    simpa only [d643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5265 (p : Pattern) (guard : d653 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d653, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d653, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d643 p = 1 := by simpa only [d653, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5264 p hg
    simpa only [d653, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5266 (p : Pattern) (guard : d654 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d653 p = 1 := by simpa only [d654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5265 p hg
    simpa only [d654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5267 (p : Pattern) (guard : d82085 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82084 p = 1 := by simpa only [d82085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5255 p hg
    simpa only [d82085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d654 p = 1 := by simpa only [d82085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5266 p hg
    simpa only [d82085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5268 (p : Pattern) (guard : d82086 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82085 p = 1 := by simpa only [d82086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5267 p hg
    simpa only [d82086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d82086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5269 (p : Pattern) (guard : d82087 p = 1) : d47767 p ≤ (-1 : Int) + d98792 p := by
  cases selected : p 50 with
  | false =>
    have hg : d82086 p = 1 := by simpa only [d82087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5268 p hg
    simpa only [d82087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4460 p hg
    simpa only [d82087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5270 (p : Pattern) (guard : d82088 p = 1) : d47768 p ≤ (-1 : Int) + d98793 p := by
  cases selected : p 49 with
  | false =>
    have hg : d82080 p = 1 := by simpa only [d82088, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5183 p hg
    simpa only [d82088, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82087 p = 1 := by simpa only [d82088, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5269 p hg
    simpa only [d82088, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5271 (p : Pattern) (guard : d528 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d309 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4946 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5272 (p : Pattern) (guard : d529 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5271 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d310 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4947 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5273 (p : Pattern) (guard : d530 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d529 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5272 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4948 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5274 (p : Pattern) (guard : d531 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5273 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5275 (p : Pattern) (guard : d532 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d531 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5274 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5276 (p : Pattern) (guard : d533 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5275 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d314 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4951 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5277 (p : Pattern) (guard : d534 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4723 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5278 (p : Pattern) (guard : d535 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4947 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d534 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5277 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5279 (p : Pattern) (guard : d536 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d535 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5278 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4725 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5280 (p : Pattern) (guard : d537 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d536 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5279 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5281 (p : Pattern) (guard : d538 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d537 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5280 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5282 (p : Pattern) (guard : d539 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d538 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5281 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4728 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5283 (p : Pattern) (guard : d540 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d533 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5276 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5282 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5284 (p : Pattern) (guard : d541 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d540 p = 1 := by simpa only [d541, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5283 p hg
    simpa only [d541, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d541, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d541, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5285 (p : Pattern) (guard : d542 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5284 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4954 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5286 (p : Pattern) (guard : d659 p = 1) : d47652 p ≤ (-1 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d659, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4519 p hg
    simpa only [d659, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d542 p = 1 := by simpa only [d659, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5285 p hg
    simpa only [d659, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5287 (p : Pattern) (guard : d543 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5091 p hg
    simpa only [d543, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d543, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5288 (p : Pattern) (guard : d660 p = 1) : d47798 p ≤ (-1 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d659 p = 1 := by simpa only [d660, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5286 p hg
    simpa only [d660, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d543 p = 1 := by simpa only [d660, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5287 p hg
    simpa only [d660, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5289 (p : Pattern) (guard : d528 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d309 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4962 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5290 (p : Pattern) (guard : d529 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5289 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d310 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4963 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5291 (p : Pattern) (guard : d530 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d529 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5290 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4964 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5292 (p : Pattern) (guard : d531 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5291 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5293 (p : Pattern) (guard : d532 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d531 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5292 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5294 (p : Pattern) (guard : d533 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5293 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d314 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4967 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5295 (p : Pattern) (guard : d534 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4739 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5296 (p : Pattern) (guard : d535 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4963 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d534 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5295 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5297 (p : Pattern) (guard : d536 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d535 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5296 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4741 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5298 (p : Pattern) (guard : d537 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d536 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5297 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5299 (p : Pattern) (guard : d538 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d537 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5298 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5300 (p : Pattern) (guard : d539 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d538 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5299 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4744 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5301 (p : Pattern) (guard : d540 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d533 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5294 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5300 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5302 (p : Pattern) (guard : d541 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d540 p = 1 := by simpa only [d541, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5301 p hg
    simpa only [d541, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d541, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d541, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5303 (p : Pattern) (guard : d542 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5302 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4970 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5304 (p : Pattern) (guard : d543 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5303 p hg
    simpa only [d543, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d543, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5305 (p : Pattern) (guard : d544 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d543 p = 1 := by simpa only [d544, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5304 p hg
    simpa only [d544, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d544, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d544, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5306 (p : Pattern) (guard : d661 p = 1) : d47799 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d660 p = 1 := by simpa only [d661, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5288 p hg
    simpa only [d661, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d661, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5305 p hg
    simpa only [d661, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5307 (p : Pattern) (guard : d662 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d661 p = 1 := by simpa only [d662, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5306 p hg
    simpa only [d662, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d662, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4556 p hg
    simpa only [d662, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5308 (p : Pattern) (guard : d663 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d662 p = 1 := by simpa only [d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5307 p hg
    simpa only [d663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d415 p = 1 := by simpa only [d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4975 p hg
    simpa only [d663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5309 (p : Pattern) (guard : d664 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d663 p = 1 := by simpa only [d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5308 p hg
    simpa only [d664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d416 p = 1 := by simpa only [d664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4976 p hg
    simpa only [d664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5310 (p : Pattern) (guard : d665 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d664 p = 1 := by simpa only [d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5309 p hg
    simpa only [d665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d417 p = 1 := by simpa only [d665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4977 p hg
    simpa only [d665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5311 (p : Pattern) (guard : d666 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d666, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d666, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d665 p = 1 := by simpa only [d666, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5310 p hg
    simpa only [d666, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5312 (p : Pattern) (guard : d667 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d667, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d667, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d666 p = 1 := by simpa only [d667, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5311 p hg
    simpa only [d667, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5313 (p : Pattern) (guard : d668 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d667 p = 1 := by simpa only [d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5312 p hg
    simpa only [d668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d420 p = 1 := by simpa only [d668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4980 p hg
    simpa only [d668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5314 (p : Pattern) (guard : d669 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d668 p = 1 := by simpa only [d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5313 p hg
    simpa only [d669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d421 p = 1 := by simpa only [d669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4981 p hg
    simpa only [d669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5315 (p : Pattern) (guard : d670 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d669 p = 1 := by simpa only [d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5314 p hg
    simpa only [d670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5316 (p : Pattern) (guard : d671 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d670 p = 1 := by simpa only [d671, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5315 p hg
    simpa only [d671, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d671, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d671, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5317 (p : Pattern) (guard : d672 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d672, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d672, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d671 p = 1 := by simpa only [d672, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5316 p hg
    simpa only [d672, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5318 (p : Pattern) (guard : d6843 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d420 p = 1 := by simpa only [d6843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4980 p hg
    simpa only [d6843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d6843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5319 (p : Pattern) (guard : d6078 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d230 p = 1 := by simpa only [d6078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4753 p hg
    simpa only [d6078, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6078, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4558 p hg
    simpa only [d6078, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5320 (p : Pattern) (guard : d6079 p = 1) : d47803 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d6078 p = 1 := by simpa only [d6079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5319 p hg
    simpa only [d6079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d71 p = 1 := by simpa only [d6079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4560 p hg
    simpa only [d6079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5321 (p : Pattern) (guard : d6080 p = 1) : d47804 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6080, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4518 p hg
    simpa only [d6080, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6079 p = 1 := by simpa only [d6080, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5320 p hg
    simpa only [d6080, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5322 (p : Pattern) (guard : d6081 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6081, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4517 p hg
    simpa only [d6081, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6080 p = 1 := by simpa only [d6081, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5321 p hg
    simpa only [d6081, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5323 (p : Pattern) (guard : d6082 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d6081 p = 1 := by simpa only [d6082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5322 p hg
    simpa only [d6082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d6082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5324 (p : Pattern) (guard : d6844 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d6843 p = 1 := by simpa only [d6844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5318 p hg
    simpa only [d6844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6082 p = 1 := by simpa only [d6844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5323 p hg
    simpa only [d6844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5325 (p : Pattern) (guard : d6845 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d6844 p = 1 := by simpa only [d6845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5324 p hg
    simpa only [d6845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d6845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5326 (p : Pattern) (guard : d6846 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6845 p = 1 := by simpa only [d6846, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5325 p hg
    simpa only [d6846, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6846, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d6846, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5327 (p : Pattern) (guard : d6847 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6847, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d6847, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6846 p = 1 := by simpa only [d6847, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5326 p hg
    simpa only [d6847, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5328 (p : Pattern) (guard : d6848 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d672 p = 1 := by simpa only [d6848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5317 p hg
    simpa only [d6848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6847 p = 1 := by simpa only [d6848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5327 p hg
    simpa only [d6848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5329 (p : Pattern) (guard : d6849 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6848 p = 1 := by simpa only [d6849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5328 p hg
    simpa only [d6849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5330 (p : Pattern) (guard : d6850 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6849 p = 1 := by simpa only [d6850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5329 p hg
    simpa only [d6850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5331 (p : Pattern) (guard : d6851 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6850 p = 1 := by simpa only [d6851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5330 p hg
    simpa only [d6851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5332 (p : Pattern) (guard : d6083 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d421 p = 1 := by simpa only [d6083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4981 p hg
    simpa only [d6083, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6082 p = 1 := by simpa only [d6083, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5323 p hg
    simpa only [d6083, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5333 (p : Pattern) (guard : d6084 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d6083 p = 1 := by simpa only [d6084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5332 p hg
    simpa only [d6084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d6084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5334 (p : Pattern) (guard : d6085 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6084 p = 1 := by simpa only [d6085, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5333 p hg
    simpa only [d6085, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6085, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d6085, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5335 (p : Pattern) (guard : d6086 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6086, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d6086, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6085 p = 1 := by simpa only [d6086, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5334 p hg
    simpa only [d6086, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5336 (p : Pattern) (guard : d682 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d673 p = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4986 p hg
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5337 (p : Pattern) (guard : d683 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d682 p = 1 := by simpa only [d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5336 p hg
    simpa only [d683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5338 (p : Pattern) (guard : d684 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d683 p = 1 := by simpa only [d684, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5337 p hg
    simpa only [d684, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d684, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d684, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5339 (p : Pattern) (guard : d685 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d685, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d685, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d684 p = 1 := by simpa only [d685, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5338 p hg
    simpa only [d685, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5340 (p : Pattern) (guard : d6852 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d6086 p = 1 := by simpa only [d6852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5335 p hg
    simpa only [d6852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d685 p = 1 := by simpa only [d6852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5339 p hg
    simpa only [d6852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5341 (p : Pattern) (guard : d6853 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6852 p = 1 := by simpa only [d6853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5340 p hg
    simpa only [d6853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5342 (p : Pattern) (guard : d6854 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6853 p = 1 := by simpa only [d6854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5341 p hg
    simpa only [d6854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5343 (p : Pattern) (guard : d6855 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6854 p = 1 := by simpa only [d6855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5342 p hg
    simpa only [d6855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5344 (p : Pattern) (guard : d6856 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6851 p = 1 := by simpa only [d6856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5331 p hg
    simpa only [d6856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6855 p = 1 := by simpa only [d6856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5343 p hg
    simpa only [d6856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5345 (p : Pattern) (guard : d82089 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6856 p = 1 := by simpa only [d82089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5344 p hg
    simpa only [d82089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5346 (p : Pattern) (guard : d674 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d421 p = 1 := by simpa only [d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4981 p hg
    simpa only [d674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d673 p = 1 := by simpa only [d674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4986 p hg
    simpa only [d674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5347 (p : Pattern) (guard : d675 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d674 p = 1 := by simpa only [d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5346 p hg
    simpa only [d675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5348 (p : Pattern) (guard : d676 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d675 p = 1 := by simpa only [d676, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5347 p hg
    simpa only [d676, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d676, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d676, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5349 (p : Pattern) (guard : d677 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d677, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d677, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d676 p = 1 := by simpa only [d677, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5348 p hg
    simpa only [d677, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5350 (p : Pattern) (guard : d5425 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d677 p = 1 := by simpa only [d5425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5349 p hg
    simpa only [d5425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d5425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5351 (p : Pattern) (guard : d5426 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d5425 p = 1 := by simpa only [d5426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5350 p hg
    simpa only [d5426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d5426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5352 (p : Pattern) (guard : d5427 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d5426 p = 1 := by simpa only [d5427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5351 p hg
    simpa only [d5427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d5427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5353 (p : Pattern) (guard : d5428 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d5427 p = 1 := by simpa only [d5428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5352 p hg
    simpa only [d5428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d5428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5354 (p : Pattern) (guard : d5429 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d5428 p = 1 := by simpa only [d5429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5353 p hg
    simpa only [d5429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d5429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5355 (p : Pattern) (guard : d5430 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d5429 p = 1 := by simpa only [d5430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5354 p hg
    simpa only [d5430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d5430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5356 (p : Pattern) (guard : d82090 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82089 p = 1 := by simpa only [d82090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5345 p hg
    simpa only [d82090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5430 p = 1 := by simpa only [d82090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5355 p hg
    simpa only [d82090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5357 (p : Pattern) (guard : d82091 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82090 p = 1 := by simpa only [d82091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5356 p hg
    simpa only [d82091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5358 (p : Pattern) (guard : d82092 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82091 p = 1 := by simpa only [d82092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5357 p hg
    simpa only [d82092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5359 (p : Pattern) (guard : d82093 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82093, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82093, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82092 p = 1 := by simpa only [d82093, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5358 p hg
    simpa only [d82093, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5360 (p : Pattern) (guard : d82094 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82093 p = 1 := by simpa only [d82094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5359 p hg
    simpa only [d82094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5361 (p : Pattern) (guard : d727 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d685 p = 1 := by simpa only [d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5339 p hg
    simpa only [d727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5362 (p : Pattern) (guard : d728 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d727 p = 1 := by simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5361 p hg
    simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5363 (p : Pattern) (guard : d729 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d728 p = 1 := by simpa only [d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5362 p hg
    simpa only [d729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5364 (p : Pattern) (guard : d730 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d729 p = 1 := by simpa only [d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5363 p hg
    simpa only [d730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5365 (p : Pattern) (guard : d731 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d730 p = 1 := by simpa only [d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5364 p hg
    simpa only [d731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5366 (p : Pattern) (guard : d732 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d731 p = 1 := by simpa only [d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5365 p hg
    simpa only [d732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5367 (p : Pattern) (guard : d733 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d732 p = 1 := by simpa only [d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5366 p hg
    simpa only [d733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5368 (p : Pattern) (guard : d734 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d733 p = 1 := by simpa only [d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5367 p hg
    simpa only [d734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5369 (p : Pattern) (guard : d735 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d734 p = 1 := by simpa only [d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5368 p hg
    simpa only [d735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5370 (p : Pattern) (guard : d736 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d736, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d736, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d735 p = 1 := by simpa only [d736, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5369 p hg
    simpa only [d736, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5371 (p : Pattern) (guard : d737 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d736 p = 1 := by simpa only [d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5370 p hg
    simpa only [d737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5372 (p : Pattern) (guard : d82095 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82094 p = 1 := by simpa only [d82095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5360 p hg
    simpa only [d82095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d737 p = 1 := by simpa only [d82095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5371 p hg
    simpa only [d82095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5373 (p : Pattern) (guard : d82096 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82095 p = 1 := by simpa only [d82096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5372 p hg
    simpa only [d82096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5374 (p : Pattern) (guard : d82097 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d82096 p = 1 := by simpa only [d82097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5373 p hg
    simpa only [d82097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5375 (p : Pattern) (guard : d82098 p = 1) : d47865 p ≤ (-1 : Int) + d98795 p := by
  cases selected : p 49 with
  | false =>
    have hg : d82097 p = 1 := by simpa only [d82098, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5374 p hg
    simpa only [d82098, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82098, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4585 p hg
    simpa only [d82098, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5376 (p : Pattern) (guard : d82099 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 48 with
  | false =>
    have hg : d82088 p = 1 := by simpa only [d82099, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5270 p hg
    simpa only [d82099, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82098 p = 1 := by simpa only [d82099, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5375 p hg
    simpa only [d82099, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5377 (p : Pattern) (guard : d82100 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82099 p = 1 := by simpa only [d82100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5376 p hg
    simpa only [d82100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5378 (p : Pattern) (guard : d82101 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82100 p = 1 := by simpa only [d82101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5377 p hg
    simpa only [d82101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5379 (p : Pattern) (guard : d82102 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82101 p = 1 := by simpa only [d82102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5378 p hg
    simpa only [d82102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5380 (p : Pattern) (guard : d82103 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82102 p = 1 := by simpa only [d82103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5379 p hg
    simpa only [d82103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5381 (p : Pattern) (guard : d82104 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82103 p = 1 := by simpa only [d82104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5380 p hg
    simpa only [d82104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5382 (p : Pattern) (guard : d82105 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82104 p = 1 := by simpa only [d82105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5381 p hg
    simpa only [d82105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5383 (p : Pattern) (guard : d82106 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d82066 p = 1 := by simpa only [d82106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5024 p hg
    simpa only [d82106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82105 p = 1 := by simpa only [d82106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5382 p hg
    simpa only [d82106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5384 (p : Pattern) (guard : d750 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4630 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4418 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5385 (p : Pattern) (guard : d751 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5384 p hg
    simpa only [d751, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d751, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5386 (p : Pattern) (guard : d752 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d751 p = 1 := by simpa only [d752, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5385 p hg
    simpa only [d752, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d752, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d752, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5387 (p : Pattern) (guard : d753 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d753, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5386 p hg
    simpa only [d753, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5388 (p : Pattern) (guard : d754 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5387 p hg
    simpa only [d754, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d754, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5389 (p : Pattern) (guard : d755 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4827 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5388 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5390 (p : Pattern) (guard : d756 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d547 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5096 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d755 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5389 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5391 (p : Pattern) (guard : d757 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5388 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5392 (p : Pattern) (guard : d758 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5389 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5391 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5393 (p : Pattern) (guard : d759 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d756 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5390 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5392 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5394 (p : Pattern) (guard : d760 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d760, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d760, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d759 p = 1 := by simpa only [d760, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5393 p hg
    simpa only [d760, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5395 (p : Pattern) (guard : d761 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d761, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d761, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d760 p = 1 := by simpa only [d761, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5394 p hg
    simpa only [d761, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5396 (p : Pattern) (guard : d762 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5391 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5397 (p : Pattern) (guard : d763 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5392 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5396 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5398 (p : Pattern) (guard : d764 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d764, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d764, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d763 p = 1 := by simpa only [d764, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5397 p hg
    simpa only [d764, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5399 (p : Pattern) (guard : d765 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d765, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5398 p hg
    simpa only [d765, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5400 (p : Pattern) (guard : d766 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d761 p = 1 := by simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5395 p hg
    simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5399 p hg
    simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5401 (p : Pattern) (guard : d767 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5399 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5402 (p : Pattern) (guard : d768 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d766 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5400 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5401 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5403 (p : Pattern) (guard : d769 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5402 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5404 (p : Pattern) (guard : d770 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d770, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5403 p hg
    simpa only [d770, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d770, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5405 (p : Pattern) (guard : d771 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d771, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d771, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d771, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5404 p hg
    simpa only [d771, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5406 (p : Pattern) (guard : d772 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5401 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5407 (p : Pattern) (guard : d773 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5406 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5408 (p : Pattern) (guard : d774 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5407 p hg
    simpa only [d774, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d774, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5409 (p : Pattern) (guard : d775 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d775, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5408 p hg
    simpa only [d775, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5410 (p : Pattern) (guard : d776 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d771 p = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5405 p hg
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5409 p hg
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5411 (p : Pattern) (guard : d777 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d776 p = 1 := by simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5410 p hg
    simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5412 (p : Pattern) (guard : d778 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d777 p = 1 := by simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5411 p hg
    simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5413 (p : Pattern) (guard : d779 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d778 p = 1 := by simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5412 p hg
    simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5414 (p : Pattern) (guard : d780 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5409 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5415 (p : Pattern) (guard : d781 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5414 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5416 (p : Pattern) (guard : d782 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5415 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5417 (p : Pattern) (guard : d783 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d782 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5416 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5418 (p : Pattern) (guard : d784 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d779 p = 1 := by simpa only [d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5413 p hg
    simpa only [d784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d783 p = 1 := by simpa only [d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5417 p hg
    simpa only [d784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5419 (p : Pattern) (guard : d785 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d784 p = 1 := by simpa only [d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5418 p hg
    simpa only [d785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5420 (p : Pattern) (guard : d786 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d785 p = 1 := by simpa only [d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5419 p hg
    simpa only [d786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5421 (p : Pattern) (guard : d787 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d786 p = 1 := by simpa only [d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5420 p hg
    simpa only [d787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5422 (p : Pattern) (guard : d788 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d787 p = 1 := by simpa only [d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5421 p hg
    simpa only [d788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5423 (p : Pattern) (guard : d789 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d788 p = 1 := by simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5422 p hg
    simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5424 (p : Pattern) (guard : d790 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d789 p = 1 := by simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5423 p hg
    simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5425 (p : Pattern) (guard : d791 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d790 p = 1 := by simpa only [d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5424 p hg
    simpa only [d791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5426 (p : Pattern) (guard : d792 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d778 p = 1 := by simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5412 p hg
    simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5427 (p : Pattern) (guard : d793 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d782 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5416 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5428 (p : Pattern) (guard : d794 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d792 p = 1 := by simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5426 p hg
    simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5427 p hg
    simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5429 (p : Pattern) (guard : d795 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5428 p hg
    simpa only [d795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5430 (p : Pattern) (guard : d796 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d795 p = 1 := by simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5429 p hg
    simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5431 (p : Pattern) (guard : d797 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d796 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5430 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5432 (p : Pattern) (guard : d798 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d797 p = 1 := by simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5431 p hg
    simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5433 (p : Pattern) (guard : d799 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d788 p = 1 := by simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5422 p hg
    simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5432 p hg
    simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5434 (p : Pattern) (guard : d800 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d789 p = 1 := by simpa only [d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5423 p hg
    simpa only [d800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d799 p = 1 := by simpa only [d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5433 p hg
    simpa only [d800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5435 (p : Pattern) (guard : d801 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d800 p = 1 := by simpa only [d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5434 p hg
    simpa only [d801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5436 (p : Pattern) (guard : d802 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d791 p = 1 := by simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5425 p hg
    simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d801 p = 1 := by simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5435 p hg
    simpa only [d802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5437 (p : Pattern) (guard : d803 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d777 p = 1 := by simpa only [d803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5411 p hg
    simpa only [d803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5438 (p : Pattern) (guard : d804 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d803 p = 1 := by simpa only [d804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5437 p hg
    simpa only [d804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5439 (p : Pattern) (guard : d805 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d781 p = 1 := by simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5415 p hg
    simpa only [d805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5440 (p : Pattern) (guard : d806 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d805 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5439 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5441 (p : Pattern) (guard : d807 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d804 p = 1 := by simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5438 p hg
    simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d806 p = 1 := by simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5440 p hg
    simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5442 (p : Pattern) (guard : d808 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d807 p = 1 := by simpa only [d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5441 p hg
    simpa only [d808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5443 (p : Pattern) (guard : d809 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d808 p = 1 := by simpa only [d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5442 p hg
    simpa only [d809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5444 (p : Pattern) (guard : d810 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d809 p = 1 := by simpa only [d810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5443 p hg
    simpa only [d810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5445 (p : Pattern) (guard : d811 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d776 p = 1 := by simpa only [d811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5410 p hg
    simpa only [d811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5446 (p : Pattern) (guard : d812 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d811 p = 1 := by simpa only [d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5445 p hg
    simpa only [d812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5447 (p : Pattern) (guard : d813 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d812 p = 1 := by simpa only [d813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5446 p hg
    simpa only [d813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5448 (p : Pattern) (guard : d814 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d780 p = 1 := by simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5414 p hg
    simpa only [d814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5449 (p : Pattern) (guard : d815 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d814 p = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5448 p hg
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5450 (p : Pattern) (guard : d816 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d815 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5449 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5451 (p : Pattern) (guard : d817 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d813 p = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5447 p hg
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d816 p = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5450 p hg
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5452 (p : Pattern) (guard : d818 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d817 p = 1 := by simpa only [d818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5451 p hg
    simpa only [d818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5453 (p : Pattern) (guard : d819 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d818 p = 1 := by simpa only [d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5452 p hg
    simpa only [d819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5454 (p : Pattern) (guard : d820 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d528 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5455 (p : Pattern) (guard : d821 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5454 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d529 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5078 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5456 (p : Pattern) (guard : d822 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5455 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5457 (p : Pattern) (guard : d823 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d822 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5456 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5458 (p : Pattern) (guard : d824 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5457 p hg
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d532 p = 1 := by simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5081 p hg
    simpa only [d824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5459 (p : Pattern) (guard : d825 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4814 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5460 (p : Pattern) (guard : d826 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5077 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5459 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5461 (p : Pattern) (guard : d827 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5460 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d535 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5084 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5462 (p : Pattern) (guard : d828 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d827 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5461 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5463 (p : Pattern) (guard : d829 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5462 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5464 (p : Pattern) (guard : d830 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5463 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d538 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5087 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5465 (p : Pattern) (guard : d831 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d824 p = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5458 p hg
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5464 p hg
    simpa only [d831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5466 (p : Pattern) (guard : d832 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d831 p = 1 := by simpa only [d832, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5465 p hg
    simpa only [d832, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d832, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d832, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5467 (p : Pattern) (guard : d833 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d832 p = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5466 p hg
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d541 p = 1 := by simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5090 p hg
    simpa only [d833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5468 (p : Pattern) (guard : d834 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d833 p = 1 := by simpa only [d834, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5467 p hg
    simpa only [d834, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d834, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d834, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5469 (p : Pattern) (guard : d835 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d834 p = 1 := by simpa only [d835, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5468 p hg
    simpa only [d835, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d835, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d835, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5470 (p : Pattern) (guard : d836 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d836, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d836, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d835 p = 1 := by simpa only [d836, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5469 p hg
    simpa only [d836, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5471 (p : Pattern) (guard : d837 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d836 p = 1 := by simpa only [d837, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5470 p hg
    simpa only [d837, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d837, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d837, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5472 (p : Pattern) (guard : d838 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d837 p = 1 := by simpa only [d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5471 p hg
    simpa only [d838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d546 p = 1 := by simpa only [d838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5095 p hg
    simpa only [d838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5473 (p : Pattern) (guard : d839 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d838 p = 1 := by simpa only [d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5472 p hg
    simpa only [d839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d547 p = 1 := by simpa only [d839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5096 p hg
    simpa only [d839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5474 (p : Pattern) (guard : d840 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d839 p = 1 := by simpa only [d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5473 p hg
    simpa only [d840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d756 p = 1 := by simpa only [d840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5390 p hg
    simpa only [d840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5475 (p : Pattern) (guard : d841 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d841, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d841, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d840 p = 1 := by simpa only [d841, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5474 p hg
    simpa only [d841, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5476 (p : Pattern) (guard : d842 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d842, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d842, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d841 p = 1 := by simpa only [d842, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5475 p hg
    simpa only [d842, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5477 (p : Pattern) (guard : d843 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d842 p = 1 := by simpa only [d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5476 p hg
    simpa only [d843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d761 p = 1 := by simpa only [d843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5395 p hg
    simpa only [d843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5478 (p : Pattern) (guard : d844 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d843 p = 1 := by simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5477 p hg
    simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d766 p = 1 := by simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5400 p hg
    simpa only [d844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5479 (p : Pattern) (guard : d845 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d844 p = 1 := by simpa only [d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5478 p hg
    simpa only [d845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5480 (p : Pattern) (guard : d846 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d845 p = 1 := by simpa only [d846, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5479 p hg
    simpa only [d846, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d846, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d846, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5481 (p : Pattern) (guard : d847 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d847, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d847, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d846 p = 1 := by simpa only [d847, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5480 p hg
    simpa only [d847, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5482 (p : Pattern) (guard : d6875 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d761 p = 1 := by simpa only [d6875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5395 p hg
    simpa only [d6875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d6875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5483 (p : Pattern) (guard : d4913 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d4913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5389 p hg
    simpa only [d4913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d4913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5484 (p : Pattern) (guard : d4914 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d4913 p = 1 := by simpa only [d4914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5483 p hg
    simpa only [d4914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d4914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5396 p hg
    simpa only [d4914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5485 (p : Pattern) (guard : d4915 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4915, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d4915, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4914 p = 1 := by simpa only [d4915, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5484 p hg
    simpa only [d4915, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5486 (p : Pattern) (guard : d4916 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4916, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d4916, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4915 p = 1 := by simpa only [d4916, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5485 p hg
    simpa only [d4916, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5487 (p : Pattern) (guard : d4917 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d4916 p = 1 := by simpa only [d4917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5486 p hg
    simpa only [d4917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d4917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5488 (p : Pattern) (guard : d6876 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d6875 p = 1 := by simpa only [d6876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5482 p hg
    simpa only [d6876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4917 p = 1 := by simpa only [d6876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5487 p hg
    simpa only [d6876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5489 (p : Pattern) (guard : d6877 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d6876 p = 1 := by simpa only [d6877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5488 p hg
    simpa only [d6877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d6877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5490 (p : Pattern) (guard : d6878 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6877 p = 1 := by simpa only [d6878, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5489 p hg
    simpa only [d6878, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6878, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d6878, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5491 (p : Pattern) (guard : d6879 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6879, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d6879, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6878 p = 1 := by simpa only [d6879, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5490 p hg
    simpa only [d6879, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5492 (p : Pattern) (guard : d6880 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d847 p = 1 := by simpa only [d6880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5481 p hg
    simpa only [d6880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6879 p = 1 := by simpa only [d6880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5491 p hg
    simpa only [d6880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5493 (p : Pattern) (guard : d6881 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6880 p = 1 := by simpa only [d6881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5492 p hg
    simpa only [d6881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5494 (p : Pattern) (guard : d6882 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6881 p = 1 := by simpa only [d6882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5493 p hg
    simpa only [d6882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5495 (p : Pattern) (guard : d6883 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6882 p = 1 := by simpa only [d6883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5494 p hg
    simpa only [d6883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5496 (p : Pattern) (guard : d4918 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d766 p = 1 := by simpa only [d4918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5400 p hg
    simpa only [d4918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4917 p = 1 := by simpa only [d4918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5487 p hg
    simpa only [d4918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5497 (p : Pattern) (guard : d4919 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d4918 p = 1 := by simpa only [d4919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5496 p hg
    simpa only [d4919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d4919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5498 (p : Pattern) (guard : d4920 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d4919 p = 1 := by simpa only [d4920, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5497 p hg
    simpa only [d4920, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d4920, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d4920, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5499 (p : Pattern) (guard : d4921 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d4921, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d4921, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d4920 p = 1 := by simpa only [d4921, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5498 p hg
    simpa only [d4921, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
