import NetHack.Soko22Hazard87.Compare120
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare30250 (p : Pattern) (guard : d259492 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259480 p = 1 := by simpa only [d259492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30224 p hg
    simpa only [d259492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259491 p = 1 := by simpa only [d259492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30249 p hg
    simpa only [d259492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30251 (p : Pattern) (guard : d259493 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259487 p = 1 := by simpa only [d259493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30240 p hg
    simpa only [d259493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259492 p = 1 := by simpa only [d259493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30250 p hg
    simpa only [d259493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30252 (p : Pattern) (guard : d259494 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259482 p = 1 := by simpa only [d259494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30226 p hg
    simpa only [d259494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259493 p = 1 := by simpa only [d259494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30251 p hg
    simpa only [d259494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30253 (p : Pattern) (guard : d259495 p = 1) : d47804 p ≤ (-1 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259495, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29015 p hg
    simpa only [d259495, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259494 p = 1 := by simpa only [d259495, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30252 p hg
    simpa only [d259495, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30254 (p : Pattern) (guard : d259496 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259496, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29014 p hg
    simpa only [d259496, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259495 p = 1 := by simpa only [d259496, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30253 p hg
    simpa only [d259496, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30255 (p : Pattern) (guard : d259497 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259491 p = 1 := by simpa only [d259497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30249 p hg
    simpa only [d259497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29056 p hg
    simpa only [d259497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30256 (p : Pattern) (guard : d259498 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259492 p = 1 := by simpa only [d259498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30250 p hg
    simpa only [d259498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259497 p = 1 := by simpa only [d259498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30255 p hg
    simpa only [d259498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30257 (p : Pattern) (guard : d259499 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259493 p = 1 := by simpa only [d259499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30251 p hg
    simpa only [d259499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259498 p = 1 := by simpa only [d259499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30256 p hg
    simpa only [d259499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30258 (p : Pattern) (guard : d259500 p = 1) : d47804 p ≤ (-1 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259500, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29015 p hg
    simpa only [d259500, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259499 p = 1 := by simpa only [d259500, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30257 p hg
    simpa only [d259500, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30259 (p : Pattern) (guard : d259501 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259501, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29014 p hg
    simpa only [d259501, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259500 p = 1 := by simpa only [d259501, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30258 p hg
    simpa only [d259501, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30260 (p : Pattern) (guard : d259502 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259496 p = 1 := by simpa only [d259502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30254 p hg
    simpa only [d259502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259501 p = 1 := by simpa only [d259502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30259 p hg
    simpa only [d259502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30261 (p : Pattern) (guard : d259503 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259486 p = 1 := by simpa only [d259503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30239 p hg
    simpa only [d259503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259491 p = 1 := by simpa only [d259503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30249 p hg
    simpa only [d259503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30262 (p : Pattern) (guard : d259504 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259503 p = 1 := by simpa only [d259504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30261 p hg
    simpa only [d259504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259497 p = 1 := by simpa only [d259504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30255 p hg
    simpa only [d259504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30263 (p : Pattern) (guard : d259505 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259493 p = 1 := by simpa only [d259505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30251 p hg
    simpa only [d259505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259504 p = 1 := by simpa only [d259505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30262 p hg
    simpa only [d259505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30264 (p : Pattern) (guard : d259506 p = 1) : d47804 p ≤ (-1 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259506, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29015 p hg
    simpa only [d259506, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259505 p = 1 := by simpa only [d259506, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30263 p hg
    simpa only [d259506, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30265 (p : Pattern) (guard : d259507 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259507, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29014 p hg
    simpa only [d259507, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259506 p = 1 := by simpa only [d259507, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30264 p hg
    simpa only [d259507, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30266 (p : Pattern) (guard : d259508 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259497 p = 1 := by simpa only [d259508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30255 p hg
    simpa only [d259508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29056 p hg
    simpa only [d259508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30267 (p : Pattern) (guard : d259509 p = 1) : d47803 p ≤ (-1 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259504 p = 1 := by simpa only [d259509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30262 p hg
    simpa only [d259509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259508 p = 1 := by simpa only [d259509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30266 p hg
    simpa only [d259509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30268 (p : Pattern) (guard : d259510 p = 1) : d47804 p ≤ (-1 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259510, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29015 p hg
    simpa only [d259510, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259509 p = 1 := by simpa only [d259510, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30267 p hg
    simpa only [d259510, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30269 (p : Pattern) (guard : d259511 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259511, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29014 p hg
    simpa only [d259511, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259510 p = 1 := by simpa only [d259511, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30268 p hg
    simpa only [d259511, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30270 (p : Pattern) (guard : d259512 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259507 p = 1 := by simpa only [d259512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30265 p hg
    simpa only [d259512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259511 p = 1 := by simpa only [d259512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30269 p hg
    simpa only [d259512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30271 (p : Pattern) (guard : d259513 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259502 p = 1 := by simpa only [d259513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30260 p hg
    simpa only [d259513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259512 p = 1 := by simpa only [d259513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30270 p hg
    simpa only [d259513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30272 (p : Pattern) (guard : d259514 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259513 p = 1 := by simpa only [d259514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30271 p hg
    simpa only [d259514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d259514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30273 (p : Pattern) (guard : d259515 p = 1) : d47807 p ≤ (-1 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259514 p = 1 := by simpa only [d259515, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30272 p hg
    simpa only [d259515, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259515, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29066 p hg
    simpa only [d259515, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30274 (p : Pattern) (guard : d259516 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259516, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259516, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259515 p = 1 := by simpa only [d259516, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30273 p hg
    simpa only [d259516, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30275 (p : Pattern) (guard : d259517 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259511 p = 1 := by simpa only [d259517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30269 p hg
    simpa only [d259517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d259517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30276 (p : Pattern) (guard : d259518 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259512 p = 1 := by simpa only [d259518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30270 p hg
    simpa only [d259518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259517 p = 1 := by simpa only [d259518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30275 p hg
    simpa only [d259518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30277 (p : Pattern) (guard : d259519 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259518 p = 1 := by simpa only [d259519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30276 p hg
    simpa only [d259519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d259519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30278 (p : Pattern) (guard : d259520 p = 1) : d47807 p ≤ (-1 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259519 p = 1 := by simpa only [d259520, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30277 p hg
    simpa only [d259520, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259520, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29066 p hg
    simpa only [d259520, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30279 (p : Pattern) (guard : d259521 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259521, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259521, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259520 p = 1 := by simpa only [d259521, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30278 p hg
    simpa only [d259521, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30280 (p : Pattern) (guard : d259522 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259516 p = 1 := by simpa only [d259522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30274 p hg
    simpa only [d259522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259521 p = 1 := by simpa only [d259522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30279 p hg
    simpa only [d259522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30281 (p : Pattern) (guard : d259523 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259522 p = 1 := by simpa only [d259523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30280 p hg
    simpa only [d259523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30282 (p : Pattern) (guard : d259524 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259523 p = 1 := by simpa only [d259524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30281 p hg
    simpa only [d259524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30283 (p : Pattern) (guard : d259525 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259524 p = 1 := by simpa only [d259525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30282 p hg
    simpa only [d259525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30284 (p : Pattern) (guard : d259526 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259517 p = 1 := by simpa only [d259526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30275 p hg
    simpa only [d259526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d259526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30285 (p : Pattern) (guard : d259527 p = 1) : d47805 p ≤ (-1 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259526 p = 1 := by simpa only [d259527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30284 p hg
    simpa only [d259527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29062 p hg
    simpa only [d259527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30286 (p : Pattern) (guard : d259528 p = 1) : d47807 p ≤ (-1 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259527 p = 1 := by simpa only [d259528, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30285 p hg
    simpa only [d259528, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259528, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29066 p hg
    simpa only [d259528, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30287 (p : Pattern) (guard : d259529 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259529, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259529, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259528 p = 1 := by simpa only [d259529, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30286 p hg
    simpa only [d259529, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30288 (p : Pattern) (guard : d259530 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259521 p = 1 := by simpa only [d259530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30279 p hg
    simpa only [d259530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259529 p = 1 := by simpa only [d259530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30287 p hg
    simpa only [d259530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30289 (p : Pattern) (guard : d259531 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259530 p = 1 := by simpa only [d259531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30288 p hg
    simpa only [d259531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30290 (p : Pattern) (guard : d259532 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259531 p = 1 := by simpa only [d259532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30289 p hg
    simpa only [d259532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30291 (p : Pattern) (guard : d259533 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259532 p = 1 := by simpa only [d259533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30290 p hg
    simpa only [d259533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30292 (p : Pattern) (guard : d259534 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259525 p = 1 := by simpa only [d259534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30283 p hg
    simpa only [d259534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259533 p = 1 := by simpa only [d259534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30291 p hg
    simpa only [d259534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30293 (p : Pattern) (guard : d259535 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259534 p = 1 := by simpa only [d259535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30292 p hg
    simpa only [d259535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30294 (p : Pattern) (guard : d259536 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259521 p = 1 := by simpa only [d259536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30279 p hg
    simpa only [d259536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30295 (p : Pattern) (guard : d259537 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259536 p = 1 := by simpa only [d259537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30294 p hg
    simpa only [d259537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30296 (p : Pattern) (guard : d259538 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259537 p = 1 := by simpa only [d259538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30295 p hg
    simpa only [d259538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30297 (p : Pattern) (guard : d259539 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259538 p = 1 := by simpa only [d259539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30296 p hg
    simpa only [d259539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30298 (p : Pattern) (guard : d259540 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259539 p = 1 := by simpa only [d259540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30297 p hg
    simpa only [d259540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30299 (p : Pattern) (guard : d259541 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259540 p = 1 := by simpa only [d259541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30298 p hg
    simpa only [d259541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30300 (p : Pattern) (guard : d259542 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259535 p = 1 := by simpa only [d259542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30293 p hg
    simpa only [d259542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259541 p = 1 := by simpa only [d259542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30299 p hg
    simpa only [d259542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30301 (p : Pattern) (guard : d259543 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259542 p = 1 := by simpa only [d259543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30300 p hg
    simpa only [d259543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30302 (p : Pattern) (guard : d259544 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259543 p = 1 := by simpa only [d259544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30301 p hg
    simpa only [d259544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30303 (p : Pattern) (guard : d259545 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259545, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259545, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259544 p = 1 := by simpa only [d259545, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30302 p hg
    simpa only [d259545, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30304 (p : Pattern) (guard : d259546 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d259546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259545 p = 1 := by simpa only [d259546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30303 p hg
    simpa only [d259546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30305 (p : Pattern) (guard : d259547 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259529 p = 1 := by simpa only [d259547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30287 p hg
    simpa only [d259547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30306 (p : Pattern) (guard : d259548 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259547 p = 1 := by simpa only [d259548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30305 p hg
    simpa only [d259548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30307 (p : Pattern) (guard : d259549 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259548 p = 1 := by simpa only [d259549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30306 p hg
    simpa only [d259549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30308 (p : Pattern) (guard : d259550 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259549 p = 1 := by simpa only [d259550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30307 p hg
    simpa only [d259550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30309 (p : Pattern) (guard : d259551 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259550 p = 1 := by simpa only [d259551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30308 p hg
    simpa only [d259551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30310 (p : Pattern) (guard : d259552 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259551 p = 1 := by simpa only [d259552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30309 p hg
    simpa only [d259552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30311 (p : Pattern) (guard : d259553 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259552 p = 1 := by simpa only [d259553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30310 p hg
    simpa only [d259553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30312 (p : Pattern) (guard : d259554 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259553 p = 1 := by simpa only [d259554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30311 p hg
    simpa only [d259554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30313 (p : Pattern) (guard : d259555 p = 1) : d47808 p ≤ (-1 : Int) + d253445 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29013 p hg
    simpa only [d259555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259554 p = 1 := by simpa only [d259555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30312 p hg
    simpa only [d259555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30314 (p : Pattern) (guard : d259556 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259556, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259556, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259555 p = 1 := by simpa only [d259556, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30313 p hg
    simpa only [d259556, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30315 (p : Pattern) (guard : d259557 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d259557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259556 p = 1 := by simpa only [d259557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30314 p hg
    simpa only [d259557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30316 (p : Pattern) (guard : d259558 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259546 p = 1 := by simpa only [d259558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30304 p hg
    simpa only [d259558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259557 p = 1 := by simpa only [d259558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30315 p hg
    simpa only [d259558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30317 (p : Pattern) (guard : d259559 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259558 p = 1 := by simpa only [d259559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30316 p hg
    simpa only [d259559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d259559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30318 (p : Pattern) (guard : d259560 p = 1) : d47809 p ≤ (-1 : Int) + d253446 p := by
  cases selected : p 50 with
  | false =>
    have hg : d259559 p = 1 := by simpa only [d259560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30317 p hg
    simpa only [d259560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29012 p hg
    simpa only [d259560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30319 (p : Pattern) (guard : d259561 p = 1) : d47865 p ≤ (-1 : Int) + d253502 p := by
  cases selected : p 49 with
  | false =>
    have hg : d259560 p = 1 := by simpa only [d259561, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30318 p hg
    simpa only [d259561, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259561, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29083 p hg
    simpa only [d259561, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30320 (p : Pattern) (guard : d259562 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 48 with
  | false =>
    have hg : d259467 p = 1 := by simpa only [d259562, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30165 p hg
    simpa only [d259562, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259561 p = 1 := by simpa only [d259562, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30319 p hg
    simpa only [d259562, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30321 (p : Pattern) (guard : d259563 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259562 p = 1 := by simpa only [d259563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30320 p hg
    simpa only [d259563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30322 (p : Pattern) (guard : d259564 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259563 p = 1 := by simpa only [d259564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30321 p hg
    simpa only [d259564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30323 (p : Pattern) (guard : d259565 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259564 p = 1 := by simpa only [d259565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30322 p hg
    simpa only [d259565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30324 (p : Pattern) (guard : d259566 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259565 p = 1 := by simpa only [d259566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30323 p hg
    simpa only [d259566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30325 (p : Pattern) (guard : d259567 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259566 p = 1 := by simpa only [d259567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30324 p hg
    simpa only [d259567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30326 (p : Pattern) (guard : d259568 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259567 p = 1 := by simpa only [d259568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30325 p hg
    simpa only [d259568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30327 (p : Pattern) (guard : d259569 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259568 p = 1 := by simpa only [d259569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30326 p hg
    simpa only [d259569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30328 (p : Pattern) (guard : d259570 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259569 p = 1 := by simpa only [d259570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30327 p hg
    simpa only [d259570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30329 (p : Pattern) (guard : d259571 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28893 p hg
    simpa only [d259571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259570 p = 1 := by simpa only [d259571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30328 p hg
    simpa only [d259571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30330 (p : Pattern) (guard : d259572 p = 1) : d47866 p ≤ (-1 : Int) + d253503 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d259290 p = 1 := by simpa only [d259572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29869 p hg
    simpa only [d259572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259571 p = 1 := by simpa only [d259572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30329 p hg
    simpa only [d259572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30331 (p : Pattern) (guard : d259573 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 225 with
  | false =>
    have hg : d258806 p = 1 := by simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29121 p hg
    simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30332 (p : Pattern) (guard : d259574 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259573 p = 1 := by simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30331 p hg
    simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30333 (p : Pattern) (guard : d259575 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29580 p hg
    simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259574 p = 1 := by simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30332 p hg
    simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30334 (p : Pattern) (guard : d259576 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258695 p = 1 := by simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28906 p hg
    simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30335 (p : Pattern) (guard : d259577 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 204 with
  | false =>
    have hg : d259575 p = 1 := by simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30333 p hg
    simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259576 p = 1 := by simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30334 p hg
    simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30336 (p : Pattern) (guard : d259578 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 202 with
  | false =>
    have hg : d259577 p = 1 := by simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30335 p hg
    simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30337 (p : Pattern) (guard : d259579 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d259578 p = 1 := by simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30336 p hg
    simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28899 p hg
    simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30338 (p : Pattern) (guard : d259580 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259579 p = 1 := by simpa only [d259580, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30337 p hg
    simpa only [d259580, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259580, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28911 p hg
    simpa only [d259580, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30339 (p : Pattern) (guard : d259581 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258184 p = 1 := by simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29969 p hg
    simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259580 p = 1 := by simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30338 p hg
    simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30340 (p : Pattern) (guard : d259582 p = 1) : d47660 p ≤ (-1 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259581 p = 1 := by simpa only [d259582, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30339 p hg
    simpa only [d259582, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259582, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28915 p hg
    simpa only [d259582, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30341 (p : Pattern) (guard : d259583 p = 1) : d47663 p ≤ (-1 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259582 p = 1 := by simpa only [d259583, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30340 p hg
    simpa only [d259583, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259583, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28917 p hg
    simpa only [d259583, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30342 (p : Pattern) (guard : d259584 p = 1) : d47664 p ≤ (-1 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259584, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28898 p hg
    simpa only [d259584, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259583 p = 1 := by simpa only [d259584, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30341 p hg
    simpa only [d259584, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30343 (p : Pattern) (guard : d259585 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259584 p = 1 := by simpa only [d259585, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30342 p hg
    simpa only [d259585, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259585, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28920 p hg
    simpa only [d259585, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30344 (p : Pattern) (guard : d259586 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258189 p = 1 := by simpa only [d259586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29974 p hg
    simpa only [d259586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259585 p = 1 := by simpa only [d259586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30343 p hg
    simpa only [d259586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30345 (p : Pattern) (guard : d259587 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259580 p = 1 := by simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30338 p hg
    simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28913 p hg
    simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30346 (p : Pattern) (guard : d259588 p = 1) : d47660 p ≤ (-1 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259587 p = 1 := by simpa only [d259588, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30345 p hg
    simpa only [d259588, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259588, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28915 p hg
    simpa only [d259588, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30347 (p : Pattern) (guard : d259589 p = 1) : d47663 p ≤ (-1 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259588 p = 1 := by simpa only [d259589, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30346 p hg
    simpa only [d259589, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259589, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28917 p hg
    simpa only [d259589, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30348 (p : Pattern) (guard : d259590 p = 1) : d47664 p ≤ (-1 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259590, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28898 p hg
    simpa only [d259590, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259589 p = 1 := by simpa only [d259590, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30347 p hg
    simpa only [d259590, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30349 (p : Pattern) (guard : d259591 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259590 p = 1 := by simpa only [d259591, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30348 p hg
    simpa only [d259591, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259591, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28920 p hg
    simpa only [d259591, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30350 (p : Pattern) (guard : d259592 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259585 p = 1 := by simpa only [d259592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30343 p hg
    simpa only [d259592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259591 p = 1 := by simpa only [d259592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30349 p hg
    simpa only [d259592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30351 (p : Pattern) (guard : d259593 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259586 p = 1 := by simpa only [d259593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30344 p hg
    simpa only [d259593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259592 p = 1 := by simpa only [d259593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30350 p hg
    simpa only [d259593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30352 (p : Pattern) (guard : d259594 p = 1) : d47617 p ≤ (-1 : Int) + d47616 p := by
  cases selected : p 201 with
  | false =>
    have hg : d259578 p = 1 := by simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30336 p hg
    simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29881 p hg
    simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30353 (p : Pattern) (guard : d259595 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259594 p = 1 := by simpa only [d259595, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30352 p hg
    simpa only [d259595, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259595, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28911 p hg
    simpa only [d259595, d47619, d253276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30354 (p : Pattern) (guard : d259596 p = 1) : d47619 p ≤ (-1 : Int) + d253276 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259595 p = 1 := by simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30353 p hg
    simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28913 p hg
    simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30355 (p : Pattern) (guard : d259597 p = 1) : d47660 p ≤ (-1 : Int) + d253307 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259596 p = 1 := by simpa only [d259597, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30354 p hg
    simpa only [d259597, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259597, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28915 p hg
    simpa only [d259597, d47660, d253307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30356 (p : Pattern) (guard : d259598 p = 1) : d47663 p ≤ (-1 : Int) + d253310 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259597 p = 1 := by simpa only [d259598, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30355 p hg
    simpa only [d259598, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259598, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28917 p hg
    simpa only [d259598, d47663, d253310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30357 (p : Pattern) (guard : d259599 p = 1) : d47664 p ≤ (-1 : Int) + d253311 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259599, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28898 p hg
    simpa only [d259599, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259598 p = 1 := by simpa only [d259599, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30356 p hg
    simpa only [d259599, d47664, d253311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30358 (p : Pattern) (guard : d259600 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259599 p = 1 := by simpa only [d259600, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30357 p hg
    simpa only [d259600, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259600, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28920 p hg
    simpa only [d259600, d47685, d253332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30359 (p : Pattern) (guard : d259601 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259585 p = 1 := by simpa only [d259601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30343 p hg
    simpa only [d259601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259600 p = 1 := by simpa only [d259601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30358 p hg
    simpa only [d259601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30360 (p : Pattern) (guard : d259602 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259591 p = 1 := by simpa only [d259602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30349 p hg
    simpa only [d259602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28922 p hg
    simpa only [d259602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30361 (p : Pattern) (guard : d259603 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259601 p = 1 := by simpa only [d259603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30359 p hg
    simpa only [d259603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259602 p = 1 := by simpa only [d259603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30360 p hg
    simpa only [d259603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30362 (p : Pattern) (guard : d259604 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259593 p = 1 := by simpa only [d259604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30351 p hg
    simpa only [d259604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259603 p = 1 := by simpa only [d259604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30361 p hg
    simpa only [d259604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30363 (p : Pattern) (guard : d259605 p = 1) : d47686 p ≤ (-1 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259605, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d259605, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259604 p = 1 := by simpa only [d259605, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30362 p hg
    simpa only [d259605, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30364 (p : Pattern) (guard : d259606 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259606, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28896 p hg
    simpa only [d259606, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259605 p = 1 := by simpa only [d259606, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30363 p hg
    simpa only [d259606, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30365 (p : Pattern) (guard : d259607 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259600 p = 1 := by simpa only [d259607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30358 p hg
    simpa only [d259607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28922 p hg
    simpa only [d259607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30366 (p : Pattern) (guard : d259608 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259607 p = 1 := by simpa only [d259608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30365 p hg
    simpa only [d259608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28922 p hg
    simpa only [d259608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30367 (p : Pattern) (guard : d259609 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259603 p = 1 := by simpa only [d259609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30361 p hg
    simpa only [d259609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259608 p = 1 := by simpa only [d259609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30366 p hg
    simpa only [d259609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30368 (p : Pattern) (guard : d259610 p = 1) : d47686 p ≤ (-1 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259610, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d259610, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259609 p = 1 := by simpa only [d259610, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30367 p hg
    simpa only [d259610, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30369 (p : Pattern) (guard : d259611 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259611, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28896 p hg
    simpa only [d259611, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259610 p = 1 := by simpa only [d259611, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30368 p hg
    simpa only [d259611, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30370 (p : Pattern) (guard : d259612 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259606 p = 1 := by simpa only [d259612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30364 p hg
    simpa only [d259612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259611 p = 1 := by simpa only [d259612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30369 p hg
    simpa only [d259612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30371 (p : Pattern) (guard : d259613 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259611 p = 1 := by simpa only [d259613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30369 p hg
    simpa only [d259613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d259613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30372 (p : Pattern) (guard : d259614 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259612 p = 1 := by simpa only [d259614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30370 p hg
    simpa only [d259614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259613 p = 1 := by simpa only [d259614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30371 p hg
    simpa only [d259614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30373 (p : Pattern) (guard : d259615 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259614 p = 1 := by simpa only [d259615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30372 p hg
    simpa only [d259615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d259615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30374 (p : Pattern) (guard : d259616 p = 1) : d47699 p ≤ (-1 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259615 p = 1 := by simpa only [d259616, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30373 p hg
    simpa only [d259616, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259616, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28932 p hg
    simpa only [d259616, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30375 (p : Pattern) (guard : d259617 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259617, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259617, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259616 p = 1 := by simpa only [d259617, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30374 p hg
    simpa only [d259617, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30376 (p : Pattern) (guard : d259618 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259613 p = 1 := by simpa only [d259618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30371 p hg
    simpa only [d259618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d259618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30377 (p : Pattern) (guard : d259619 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259618 p = 1 := by simpa only [d259619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30376 p hg
    simpa only [d259619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d259619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30378 (p : Pattern) (guard : d259620 p = 1) : d47699 p ≤ (-1 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259619 p = 1 := by simpa only [d259620, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30377 p hg
    simpa only [d259620, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259620, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28932 p hg
    simpa only [d259620, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30379 (p : Pattern) (guard : d259621 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259621, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259621, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259620 p = 1 := by simpa only [d259621, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30378 p hg
    simpa only [d259621, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30380 (p : Pattern) (guard : d259622 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259617 p = 1 := by simpa only [d259622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30375 p hg
    simpa only [d259622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259621 p = 1 := by simpa only [d259622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30379 p hg
    simpa only [d259622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30381 (p : Pattern) (guard : d259623 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259622 p = 1 := by simpa only [d259623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30380 p hg
    simpa only [d259623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30382 (p : Pattern) (guard : d259624 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259623 p = 1 := by simpa only [d259624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30381 p hg
    simpa only [d259624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30383 (p : Pattern) (guard : d259625 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259624 p = 1 := by simpa only [d259625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30382 p hg
    simpa only [d259625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30384 (p : Pattern) (guard : d259626 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259621 p = 1 := by simpa only [d259626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30379 p hg
    simpa only [d259626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30385 (p : Pattern) (guard : d259627 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259626 p = 1 := by simpa only [d259627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30384 p hg
    simpa only [d259627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30386 (p : Pattern) (guard : d259628 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259627 p = 1 := by simpa only [d259628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30385 p hg
    simpa only [d259628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30387 (p : Pattern) (guard : d259629 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259628 p = 1 := by simpa only [d259629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30386 p hg
    simpa only [d259629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30388 (p : Pattern) (guard : d259630 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259625 p = 1 := by simpa only [d259630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30383 p hg
    simpa only [d259630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259629 p = 1 := by simpa only [d259630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30387 p hg
    simpa only [d259630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30389 (p : Pattern) (guard : d259631 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259630 p = 1 := by simpa only [d259631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30388 p hg
    simpa only [d259631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30390 (p : Pattern) (guard : d259632 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259631 p = 1 := by simpa only [d259632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30389 p hg
    simpa only [d259632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30391 (p : Pattern) (guard : d259633 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259632 p = 1 := by simpa only [d259633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30390 p hg
    simpa only [d259633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30392 (p : Pattern) (guard : d259634 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259633 p = 1 := by simpa only [d259634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30391 p hg
    simpa only [d259634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30393 (p : Pattern) (guard : d259635 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259634 p = 1 := by simpa only [d259635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30392 p hg
    simpa only [d259635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30394 (p : Pattern) (guard : d259636 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259635 p = 1 := by simpa only [d259636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30393 p hg
    simpa only [d259636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30395 (p : Pattern) (guard : d259637 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259636 p = 1 := by simpa only [d259637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30394 p hg
    simpa only [d259637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30396 (p : Pattern) (guard : d259638 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259624 p = 1 := by simpa only [d259638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30382 p hg
    simpa only [d259638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30397 (p : Pattern) (guard : d259639 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259628 p = 1 := by simpa only [d259639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30386 p hg
    simpa only [d259639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30398 (p : Pattern) (guard : d259640 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259638 p = 1 := by simpa only [d259640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30396 p hg
    simpa only [d259640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259639 p = 1 := by simpa only [d259640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30397 p hg
    simpa only [d259640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30399 (p : Pattern) (guard : d259641 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259640 p = 1 := by simpa only [d259641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30398 p hg
    simpa only [d259641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30400 (p : Pattern) (guard : d259642 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259641 p = 1 := by simpa only [d259642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30399 p hg
    simpa only [d259642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30401 (p : Pattern) (guard : d259643 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259642 p = 1 := by simpa only [d259643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30400 p hg
    simpa only [d259643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30402 (p : Pattern) (guard : d259644 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259643 p = 1 := by simpa only [d259644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30401 p hg
    simpa only [d259644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30403 (p : Pattern) (guard : d259645 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d259634 p = 1 := by simpa only [d259645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30392 p hg
    simpa only [d259645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259644 p = 1 := by simpa only [d259645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30402 p hg
    simpa only [d259645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30404 (p : Pattern) (guard : d259646 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d259635 p = 1 := by simpa only [d259646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30393 p hg
    simpa only [d259646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259645 p = 1 := by simpa only [d259646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30403 p hg
    simpa only [d259646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30405 (p : Pattern) (guard : d259647 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259646 p = 1 := by simpa only [d259647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30404 p hg
    simpa only [d259647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30406 (p : Pattern) (guard : d259648 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259637 p = 1 := by simpa only [d259648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30395 p hg
    simpa only [d259648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259647 p = 1 := by simpa only [d259648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30405 p hg
    simpa only [d259648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30407 (p : Pattern) (guard : d259649 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259623 p = 1 := by simpa only [d259649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30381 p hg
    simpa only [d259649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30408 (p : Pattern) (guard : d259650 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259649 p = 1 := by simpa only [d259650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30407 p hg
    simpa only [d259650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30409 (p : Pattern) (guard : d259651 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259627 p = 1 := by simpa only [d259651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30385 p hg
    simpa only [d259651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30410 (p : Pattern) (guard : d259652 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259651 p = 1 := by simpa only [d259652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30409 p hg
    simpa only [d259652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30411 (p : Pattern) (guard : d259653 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259650 p = 1 := by simpa only [d259653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30408 p hg
    simpa only [d259653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259652 p = 1 := by simpa only [d259653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30410 p hg
    simpa only [d259653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30412 (p : Pattern) (guard : d259654 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259653 p = 1 := by simpa only [d259654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30411 p hg
    simpa only [d259654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30413 (p : Pattern) (guard : d259655 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259654 p = 1 := by simpa only [d259655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30412 p hg
    simpa only [d259655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30414 (p : Pattern) (guard : d259656 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259655 p = 1 := by simpa only [d259656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30413 p hg
    simpa only [d259656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30415 (p : Pattern) (guard : d259657 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259622 p = 1 := by simpa only [d259657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30380 p hg
    simpa only [d259657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30416 (p : Pattern) (guard : d259658 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259657 p = 1 := by simpa only [d259658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30415 p hg
    simpa only [d259658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30417 (p : Pattern) (guard : d259659 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259658 p = 1 := by simpa only [d259659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30416 p hg
    simpa only [d259659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30418 (p : Pattern) (guard : d259660 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259626 p = 1 := by simpa only [d259660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30384 p hg
    simpa only [d259660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30419 (p : Pattern) (guard : d259661 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259660 p = 1 := by simpa only [d259661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30418 p hg
    simpa only [d259661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30420 (p : Pattern) (guard : d259662 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259661 p = 1 := by simpa only [d259662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30419 p hg
    simpa only [d259662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30421 (p : Pattern) (guard : d259663 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259659 p = 1 := by simpa only [d259663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30417 p hg
    simpa only [d259663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259662 p = 1 := by simpa only [d259663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30420 p hg
    simpa only [d259663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30422 (p : Pattern) (guard : d259664 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259663 p = 1 := by simpa only [d259664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30421 p hg
    simpa only [d259664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30423 (p : Pattern) (guard : d259665 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259664 p = 1 := by simpa only [d259665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30422 p hg
    simpa only [d259665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30424 (p : Pattern) (guard : d258476 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28922 p hg
    simpa only [d258476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258189 p = 1 := by simpa only [d258476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29974 p hg
    simpa only [d258476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30425 (p : Pattern) (guard : d259666 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d258476 p = 1 := by simpa only [d259666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30424 p hg
    simpa only [d259666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259586 p = 1 := by simpa only [d259666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30344 p hg
    simpa only [d259666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30426 (p : Pattern) (guard : d259667 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259666 p = 1 := by simpa only [d259667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30425 p hg
    simpa only [d259667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259593 p = 1 := by simpa only [d259667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30351 p hg
    simpa only [d259667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30427 (p : Pattern) (guard : d259668 p = 1) : d47686 p ≤ (-1 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259668, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d259668, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259667 p = 1 := by simpa only [d259668, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30426 p hg
    simpa only [d259668, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30428 (p : Pattern) (guard : d259669 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259669, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28896 p hg
    simpa only [d259669, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259668 p = 1 := by simpa only [d259669, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30427 p hg
    simpa only [d259669, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30429 (p : Pattern) (guard : d259670 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259592 p = 1 := by simpa only [d259670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30350 p hg
    simpa only [d259670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259602 p = 1 := by simpa only [d259670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30360 p hg
    simpa only [d259670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30430 (p : Pattern) (guard : d259671 p = 1) : d47685 p ≤ (-1 : Int) + d253332 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259593 p = 1 := by simpa only [d259671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30351 p hg
    simpa only [d259671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259670 p = 1 := by simpa only [d259671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30429 p hg
    simpa only [d259671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30431 (p : Pattern) (guard : d259672 p = 1) : d47686 p ≤ (-1 : Int) + d253333 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259672, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28897 p hg
    simpa only [d259672, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259671 p = 1 := by simpa only [d259672, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30430 p hg
    simpa only [d259672, d47686, d253333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30432 (p : Pattern) (guard : d259673 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259673, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28896 p hg
    simpa only [d259673, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259672 p = 1 := by simpa only [d259673, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30431 p hg
    simpa only [d259673, d47687, d253334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30433 (p : Pattern) (guard : d259674 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259669 p = 1 := by simpa only [d259674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30428 p hg
    simpa only [d259674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259673 p = 1 := by simpa only [d259674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30432 p hg
    simpa only [d259674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30434 (p : Pattern) (guard : d259675 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259674 p = 1 := by simpa only [d259675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30433 p hg
    simpa only [d259675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259612 p = 1 := by simpa only [d259675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30370 p hg
    simpa only [d259675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30435 (p : Pattern) (guard : d259676 p = 1) : d47687 p ≤ (-1 : Int) + d253334 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259675 p = 1 := by simpa only [d259676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30434 p hg
    simpa only [d259676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28928 p hg
    simpa only [d259676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30436 (p : Pattern) (guard : d259677 p = 1) : d47699 p ≤ (-1 : Int) + d253346 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259676 p = 1 := by simpa only [d259677, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30435 p hg
    simpa only [d259677, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259677, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28932 p hg
    simpa only [d259677, d47699, d253346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30437 (p : Pattern) (guard : d259678 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259678, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28895 p hg
    simpa only [d259678, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259677 p = 1 := by simpa only [d259678, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30436 p hg
    simpa only [d259678, d47700, d253347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30438 (p : Pattern) (guard : d259679 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259678 p = 1 := by simpa only [d259679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30437 p hg
    simpa only [d259679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259617 p = 1 := by simpa only [d259679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30375 p hg
    simpa only [d259679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30439 (p : Pattern) (guard : d259680 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259679 p = 1 := by simpa only [d259680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30438 p hg
    simpa only [d259680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30440 (p : Pattern) (guard : d259681 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259680 p = 1 := by simpa only [d259681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30439 p hg
    simpa only [d259681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30441 (p : Pattern) (guard : d259682 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259681 p = 1 := by simpa only [d259682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30440 p hg
    simpa only [d259682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30442 (p : Pattern) (guard : d259683 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259682 p = 1 := by simpa only [d259683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30441 p hg
    simpa only [d259683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259625 p = 1 := by simpa only [d259683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30383 p hg
    simpa only [d259683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30443 (p : Pattern) (guard : d259684 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259683 p = 1 := by simpa only [d259684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30442 p hg
    simpa only [d259684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30444 (p : Pattern) (guard : d259685 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259617 p = 1 := by simpa only [d259685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30375 p hg
    simpa only [d259685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30445 (p : Pattern) (guard : d259686 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259685 p = 1 := by simpa only [d259686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30444 p hg
    simpa only [d259686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30446 (p : Pattern) (guard : d259687 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259686 p = 1 := by simpa only [d259687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30445 p hg
    simpa only [d259687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30447 (p : Pattern) (guard : d259688 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259687 p = 1 := by simpa only [d259688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30446 p hg
    simpa only [d259688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30448 (p : Pattern) (guard : d259689 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259688 p = 1 := by simpa only [d259689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30447 p hg
    simpa only [d259689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30449 (p : Pattern) (guard : d259690 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259689 p = 1 := by simpa only [d259690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30448 p hg
    simpa only [d259690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30450 (p : Pattern) (guard : d259691 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259684 p = 1 := by simpa only [d259691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30443 p hg
    simpa only [d259691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259690 p = 1 := by simpa only [d259691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30449 p hg
    simpa only [d259691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30451 (p : Pattern) (guard : d259692 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d259665 p = 1 := by simpa only [d259692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30423 p hg
    simpa only [d259692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259691 p = 1 := by simpa only [d259692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30450 p hg
    simpa only [d259692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30452 (p : Pattern) (guard : d259693 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d259656 p = 1 := by simpa only [d259693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30414 p hg
    simpa only [d259693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259692 p = 1 := by simpa only [d259693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30451 p hg
    simpa only [d259693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30453 (p : Pattern) (guard : d259694 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259693 p = 1 := by simpa only [d259694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30452 p hg
    simpa only [d259694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30454 (p : Pattern) (guard : d259695 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259649 p = 1 := by simpa only [d259695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30407 p hg
    simpa only [d259695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30455 (p : Pattern) (guard : d259696 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259651 p = 1 := by simpa only [d259696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30409 p hg
    simpa only [d259696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30456 (p : Pattern) (guard : d259697 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259695 p = 1 := by simpa only [d259697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30454 p hg
    simpa only [d259697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259696 p = 1 := by simpa only [d259697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30455 p hg
    simpa only [d259697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30457 (p : Pattern) (guard : d259698 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259697 p = 1 := by simpa only [d259698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30456 p hg
    simpa only [d259698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30458 (p : Pattern) (guard : d259699 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259698 p = 1 := by simpa only [d259699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30457 p hg
    simpa only [d259699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30459 (p : Pattern) (guard : d259700 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259699 p = 1 := by simpa only [d259700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30458 p hg
    simpa only [d259700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30460 (p : Pattern) (guard : d259701 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259658 p = 1 := by simpa only [d259701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30416 p hg
    simpa only [d259701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30461 (p : Pattern) (guard : d259702 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259661 p = 1 := by simpa only [d259702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30419 p hg
    simpa only [d259702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30462 (p : Pattern) (guard : d259703 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259701 p = 1 := by simpa only [d259703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30460 p hg
    simpa only [d259703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259702 p = 1 := by simpa only [d259703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30461 p hg
    simpa only [d259703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30463 (p : Pattern) (guard : d259704 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259703 p = 1 := by simpa only [d259704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30462 p hg
    simpa only [d259704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30464 (p : Pattern) (guard : d259705 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259704 p = 1 := by simpa only [d259705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30463 p hg
    simpa only [d259705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30465 (p : Pattern) (guard : d259706 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259681 p = 1 := by simpa only [d259706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30440 p hg
    simpa only [d259706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30466 (p : Pattern) (guard : d259707 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259706 p = 1 := by simpa only [d259707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30465 p hg
    simpa only [d259707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259638 p = 1 := by simpa only [d259707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30396 p hg
    simpa only [d259707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30467 (p : Pattern) (guard : d259708 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259707 p = 1 := by simpa only [d259708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30466 p hg
    simpa only [d259708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30468 (p : Pattern) (guard : d259709 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259687 p = 1 := by simpa only [d259709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30446 p hg
    simpa only [d259709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30469 (p : Pattern) (guard : d259710 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259709 p = 1 := by simpa only [d259710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30468 p hg
    simpa only [d259710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30470 (p : Pattern) (guard : d259711 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d259710 p = 1 := by simpa only [d259711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30469 p hg
    simpa only [d259711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30471 (p : Pattern) (guard : d259712 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259708 p = 1 := by simpa only [d259712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30467 p hg
    simpa only [d259712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259711 p = 1 := by simpa only [d259712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30470 p hg
    simpa only [d259712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30472 (p : Pattern) (guard : d259713 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d259705 p = 1 := by simpa only [d259713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30464 p hg
    simpa only [d259713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259712 p = 1 := by simpa only [d259713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30471 p hg
    simpa only [d259713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30473 (p : Pattern) (guard : d259714 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d259700 p = 1 := by simpa only [d259714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30459 p hg
    simpa only [d259714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259713 p = 1 := by simpa only [d259714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30472 p hg
    simpa only [d259714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30474 (p : Pattern) (guard : d259715 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d259693 p = 1 := by simpa only [d259715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30452 p hg
    simpa only [d259715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259714 p = 1 := by simpa only [d259715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30473 p hg
    simpa only [d259715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30475 (p : Pattern) (guard : d259716 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d259694 p = 1 := by simpa only [d259716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30453 p hg
    simpa only [d259716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259715 p = 1 := by simpa only [d259716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30474 p hg
    simpa only [d259716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30476 (p : Pattern) (guard : d259717 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259629 p = 1 := by simpa only [d259717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30387 p hg
    simpa only [d259717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30477 (p : Pattern) (guard : d259718 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259717 p = 1 := by simpa only [d259718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30476 p hg
    simpa only [d259718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30478 (p : Pattern) (guard : d259719 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259718 p = 1 := by simpa only [d259719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30477 p hg
    simpa only [d259719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30479 (p : Pattern) (guard : d259720 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259719 p = 1 := by simpa only [d259720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30478 p hg
    simpa only [d259720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30480 (p : Pattern) (guard : d259721 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259720 p = 1 := by simpa only [d259721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30479 p hg
    simpa only [d259721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30481 (p : Pattern) (guard : d259722 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d259634 p = 1 := by simpa only [d259722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30392 p hg
    simpa only [d259722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259721 p = 1 := by simpa only [d259722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30480 p hg
    simpa only [d259722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30482 (p : Pattern) (guard : d259723 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259639 p = 1 := by simpa only [d259723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30397 p hg
    simpa only [d259723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30483 (p : Pattern) (guard : d259724 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259723 p = 1 := by simpa only [d259724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30482 p hg
    simpa only [d259724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30484 (p : Pattern) (guard : d259725 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259724 p = 1 := by simpa only [d259725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30483 p hg
    simpa only [d259725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30485 (p : Pattern) (guard : d259726 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259725 p = 1 := by simpa only [d259726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30484 p hg
    simpa only [d259726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30486 (p : Pattern) (guard : d259727 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259726 p = 1 := by simpa only [d259727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30485 p hg
    simpa only [d259727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30487 (p : Pattern) (guard : d259728 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 71 with
  | false =>
    have hg : d259721 p = 1 := by simpa only [d259728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30480 p hg
    simpa only [d259728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259727 p = 1 := by simpa only [d259728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30486 p hg
    simpa only [d259728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30488 (p : Pattern) (guard : d259729 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 70 with
  | false =>
    have hg : d259722 p = 1 := by simpa only [d259729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30481 p hg
    simpa only [d259729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259728 p = 1 := by simpa only [d259729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30487 p hg
    simpa only [d259729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30489 (p : Pattern) (guard : d259730 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 69 with
  | false =>
    have hg : d259716 p = 1 := by simpa only [d259730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30475 p hg
    simpa only [d259730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259729 p = 1 := by simpa only [d259730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30488 p hg
    simpa only [d259730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30490 (p : Pattern) (guard : d259731 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 51 with
  | false =>
    have hg : d259730 p = 1 := by simpa only [d259731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30489 p hg
    simpa only [d259731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28894 p hg
    simpa only [d259731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30491 (p : Pattern) (guard : d259732 p = 1) : d47700 p ≤ (-1 : Int) + d253347 p := by
  cases selected : p 50 with
  | false =>
    have hg : d259648 p = 1 := by simpa only [d259732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30406 p hg
    simpa only [d259732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259731 p = 1 := by simpa only [d259732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30490 p hg
    simpa only [d259732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30492 (p : Pattern) (guard : d258476 p = 1) : d47755 p ≤ (-1 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28984 p hg
    simpa only [d258476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258189 p = 1 := by simpa only [d258476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30055 p hg
    simpa only [d258476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30493 (p : Pattern) (guard : d259573 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 225 with
  | false =>
    have hg : d258806 p = 1 := by simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29178 p hg
    simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30494 (p : Pattern) (guard : d259574 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259573 p = 1 := by simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30493 p hg
    simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30495 (p : Pattern) (guard : d259575 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29674 p hg
    simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259574 p = 1 := by simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30494 p hg
    simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30496 (p : Pattern) (guard : d259576 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258695 p = 1 := by simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28969 p hg
    simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30497 (p : Pattern) (guard : d259577 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d259575 p = 1 := by simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30495 p hg
    simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259576 p = 1 := by simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30496 p hg
    simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30498 (p : Pattern) (guard : d259578 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 202 with
  | false =>
    have hg : d259577 p = 1 := by simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30497 p hg
    simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare30499 (p : Pattern) (guard : d259579 p = 1) : d47706 p ≤ (-1 : Int) + d47705 p := by
  cases selected : p 201 with
  | false =>
    have hg : d259578 p = 1 := by simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30498 p hg
    simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare28962 p hg
    simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
