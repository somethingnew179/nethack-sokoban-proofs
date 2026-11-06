import NetHack.Soko22Hazard87.Compare093
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare23500 (p : Pattern) (guard : d179265 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare23501 (p : Pattern) (guard : d179266 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179265 p = 1 := by simpa only [d179266, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23500 p hg
    simpa only [d179266, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179266, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23387 p hg
    simpa only [d179266, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23502 (p : Pattern) (guard : d179267 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d179267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179266 p = 1 := by simpa only [d179267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23501 p hg
    simpa only [d179267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23503 (p : Pattern) (guard : d179268 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179267 p = 1 := by simpa only [d179268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23502 p hg
    simpa only [d179268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d179268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23504 (p : Pattern) (guard : d179417 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179268 p = 1 := by simpa only [d179417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23503 p hg
    simpa only [d179417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d179417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23505 (p : Pattern) (guard : d179418 p = 1) : d48362 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179418, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23384 p hg
    simpa only [d179418, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179417 p = 1 := by simpa only [d179418, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23504 p hg
    simpa only [d179418, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23506 (p : Pattern) (guard : d179419 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179419, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23383 p hg
    simpa only [d179419, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179418 p = 1 := by simpa only [d179419, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23505 p hg
    simpa only [d179419, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23507 (p : Pattern) (guard : d179421 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179419 p = 1 := by simpa only [d179421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23506 p hg
    simpa only [d179421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d179421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23508 (p : Pattern) (guard : d179426 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179421 p = 1 := by simpa only [d179426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23507 p hg
    simpa only [d179426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d179426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23509 (p : Pattern) (guard : d179427 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179426 p = 1 := by simpa only [d179427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23508 p hg
    simpa only [d179427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d179427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23510 (p : Pattern) (guard : d179428 p = 1) : d48365 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179427 p = 1 := by simpa only [d179428, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23509 p hg
    simpa only [d179428, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179428, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23398 p hg
    simpa only [d179428, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23511 (p : Pattern) (guard : d179429 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179429, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d179429, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179428 p = 1 := by simpa only [d179429, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23510 p hg
    simpa only [d179429, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23512 (p : Pattern) (guard : d179434 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179429 p = 1 := by simpa only [d179434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23511 p hg
    simpa only [d179434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23513 (p : Pattern) (guard : d179435 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179434 p = 1 := by simpa only [d179435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23512 p hg
    simpa only [d179435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23514 (p : Pattern) (guard : d179436 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179435 p = 1 := by simpa only [d179436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23513 p hg
    simpa only [d179436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23515 (p : Pattern) (guard : d179437 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179436 p = 1 := by simpa only [d179437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23514 p hg
    simpa only [d179437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23516 (p : Pattern) (guard : d179440 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179437 p = 1 := by simpa only [d179440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23515 p hg
    simpa only [d179440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23517 (p : Pattern) (guard : d180460 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179440 p = 1 := by simpa only [d180460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23516 p hg
    simpa only [d180460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23518 (p : Pattern) (guard : d180461 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180460 p = 1 := by simpa only [d180461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23517 p hg
    simpa only [d180461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23519 (p : Pattern) (guard : d180462 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180461 p = 1 := by simpa only [d180462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23518 p hg
    simpa only [d180462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23520 (p : Pattern) (guard : d180463 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180463, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180462 p = 1 := by simpa only [d180463, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23519 p hg
    simpa only [d180463, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23521 (p : Pattern) (guard : d180464 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180464, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180464, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180463 p = 1 := by simpa only [d180464, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23520 p hg
    simpa only [d180464, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23522 (p : Pattern) (guard : d180465 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180464 p = 1 := by simpa only [d180465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23521 p hg
    simpa only [d180465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23523 (p : Pattern) (guard : d180466 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180465 p = 1 := by simpa only [d180466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23522 p hg
    simpa only [d180466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23524 (p : Pattern) (guard : d180467 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180466 p = 1 := by simpa only [d180467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23523 p hg
    simpa only [d180467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23525 (p : Pattern) (guard : d180468 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d180467 p = 1 := by simpa only [d180468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23524 p hg
    simpa only [d180468, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180468, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180468, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23526 (p : Pattern) (guard : d180469 p = 1) : d48387 p ≤ (0 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d180468 p = 1 := by simpa only [d180469, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23525 p hg
    simpa only [d180469, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180469, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23415 p hg
    simpa only [d180469, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23527 (p : Pattern) (guard : d180470 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d180459 p = 1 := by simpa only [d180470, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23499 p hg
    simpa only [d180470, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180469 p = 1 := by simpa only [d180470, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23526 p hg
    simpa only [d180470, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23528 (p : Pattern) (guard : d180471 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180470 p = 1 := by simpa only [d180471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23527 p hg
    simpa only [d180471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23529 (p : Pattern) (guard : d180472 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180471 p = 1 := by simpa only [d180472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23528 p hg
    simpa only [d180472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23530 (p : Pattern) (guard : d180473 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180472 p = 1 := by simpa only [d180473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23529 p hg
    simpa only [d180473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23531 (p : Pattern) (guard : d180474 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180473 p = 1 := by simpa only [d180474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23530 p hg
    simpa only [d180474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23532 (p : Pattern) (guard : d180475 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180474 p = 1 := by simpa only [d180475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23531 p hg
    simpa only [d180475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23533 (p : Pattern) (guard : d180476 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180475 p = 1 := by simpa only [d180476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23532 p hg
    simpa only [d180476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23534 (p : Pattern) (guard : d180477 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180476 p = 1 := by simpa only [d180477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23533 p hg
    simpa only [d180477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23535 (p : Pattern) (guard : d180478 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d180451 p = 1 := by simpa only [d180478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23424 p hg
    simpa only [d180478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180477 p = 1 := by simpa only [d180478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23534 p hg
    simpa only [d180478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23536 (p : Pattern) (guard : d179468 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare23537 (p : Pattern) (guard : d179469 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179468 p = 1 := by simpa only [d179469, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23536 p hg
    simpa only [d179469, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179469, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23292 p hg
    simpa only [d179469, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23538 (p : Pattern) (guard : d179470 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179469 p = 1 := by simpa only [d179470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23537 p hg
    simpa only [d179470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23539 (p : Pattern) (guard : d179471 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179470 p = 1 := by simpa only [d179471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23538 p hg
    simpa only [d179471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23540 (p : Pattern) (guard : d179480 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare23541 (p : Pattern) (guard : d179481 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179480 p = 1 := by simpa only [d179481, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23540 p hg
    simpa only [d179481, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179481, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23292 p hg
    simpa only [d179481, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23542 (p : Pattern) (guard : d179482 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179481 p = 1 := by simpa only [d179482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23541 p hg
    simpa only [d179482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23543 (p : Pattern) (guard : d179483 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179482 p = 1 := by simpa only [d179483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23542 p hg
    simpa only [d179483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23544 (p : Pattern) (guard : d179484 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179471 p = 1 := by simpa only [d179484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23539 p hg
    simpa only [d179484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179483 p = 1 := by simpa only [d179484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23543 p hg
    simpa only [d179484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23545 (p : Pattern) (guard : d179485 p = 1) : d48326 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179485, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23289 p hg
    simpa only [d179485, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179484 p = 1 := by simpa only [d179485, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23544 p hg
    simpa only [d179485, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23546 (p : Pattern) (guard : d179486 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179486, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23288 p hg
    simpa only [d179486, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179485 p = 1 := by simpa only [d179486, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23545 p hg
    simpa only [d179486, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23547 (p : Pattern) (guard : d179487 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179483 p = 1 := by simpa only [d179487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23543 p hg
    simpa only [d179487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23548 (p : Pattern) (guard : d179488 p = 1) : d48326 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179488, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23289 p hg
    simpa only [d179488, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179487 p = 1 := by simpa only [d179488, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23547 p hg
    simpa only [d179488, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23549 (p : Pattern) (guard : d179489 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179489, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23288 p hg
    simpa only [d179489, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179488 p = 1 := by simpa only [d179489, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23548 p hg
    simpa only [d179489, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23550 (p : Pattern) (guard : d179490 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179486 p = 1 := by simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23546 p hg
    simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179489 p = 1 := by simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23549 p hg
    simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23551 (p : Pattern) (guard : d179491 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179489 p = 1 := by simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23549 p hg
    simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23552 (p : Pattern) (guard : d179492 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179490 p = 1 := by simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23550 p hg
    simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179491 p = 1 := by simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23551 p hg
    simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23553 (p : Pattern) (guard : d179493 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179492 p = 1 := by simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23552 p hg
    simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23554 (p : Pattern) (guard : d179494 p = 1) : d48338 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179493 p = 1 := by simpa only [d179494, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23553 p hg
    simpa only [d179494, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179494, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d179494, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23555 (p : Pattern) (guard : d179495 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179495, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d179495, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179494 p = 1 := by simpa only [d179495, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23554 p hg
    simpa only [d179495, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23556 (p : Pattern) (guard : d179496 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179491 p = 1 := by simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23551 p hg
    simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23557 (p : Pattern) (guard : d179497 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179496 p = 1 := by simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23556 p hg
    simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23558 (p : Pattern) (guard : d179498 p = 1) : d48338 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179497 p = 1 := by simpa only [d179498, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23557 p hg
    simpa only [d179498, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179498, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d179498, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23559 (p : Pattern) (guard : d179499 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179499, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d179499, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179498 p = 1 := by simpa only [d179499, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23558 p hg
    simpa only [d179499, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23560 (p : Pattern) (guard : d179500 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179495 p = 1 := by simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23555 p hg
    simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179499 p = 1 := by simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23559 p hg
    simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23561 (p : Pattern) (guard : d179501 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179500 p = 1 := by simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23560 p hg
    simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23562 (p : Pattern) (guard : d179502 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179501 p = 1 := by simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23561 p hg
    simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23563 (p : Pattern) (guard : d179503 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179502 p = 1 := by simpa only [d179503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23562 p hg
    simpa only [d179503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23564 (p : Pattern) (guard : d179504 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179499 p = 1 := by simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23559 p hg
    simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23565 (p : Pattern) (guard : d179505 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179504 p = 1 := by simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23564 p hg
    simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23566 (p : Pattern) (guard : d179506 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179505 p = 1 := by simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23565 p hg
    simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23567 (p : Pattern) (guard : d179507 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179506 p = 1 := by simpa only [d179507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23566 p hg
    simpa only [d179507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23568 (p : Pattern) (guard : d179508 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179503 p = 1 := by simpa only [d179508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23563 p hg
    simpa only [d179508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179507 p = 1 := by simpa only [d179508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23567 p hg
    simpa only [d179508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23569 (p : Pattern) (guard : d179509 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179508 p = 1 := by simpa only [d179509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23568 p hg
    simpa only [d179509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23570 (p : Pattern) (guard : d179510 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179509 p = 1 := by simpa only [d179510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23569 p hg
    simpa only [d179510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23571 (p : Pattern) (guard : d179511 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179510 p = 1 := by simpa only [d179511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23570 p hg
    simpa only [d179511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23572 (p : Pattern) (guard : d179512 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179511 p = 1 := by simpa only [d179512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23571 p hg
    simpa only [d179512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23573 (p : Pattern) (guard : d179513 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179513, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179513, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179512 p = 1 := by simpa only [d179513, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23572 p hg
    simpa only [d179513, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23574 (p : Pattern) (guard : d179486 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179486, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23317 p hg
    simpa only [d179486, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179485 p = 1 := by simpa only [d179486, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23545 p hg
    simpa only [d179486, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23575 (p : Pattern) (guard : d179489 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179489, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23317 p hg
    simpa only [d179489, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179488 p = 1 := by simpa only [d179489, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23548 p hg
    simpa only [d179489, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23576 (p : Pattern) (guard : d179490 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179486 p = 1 := by simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23574 p hg
    simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179489 p = 1 := by simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23575 p hg
    simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23577 (p : Pattern) (guard : d179491 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179489 p = 1 := by simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23575 p hg
    simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23578 (p : Pattern) (guard : d179492 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179490 p = 1 := by simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23576 p hg
    simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179491 p = 1 := by simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23577 p hg
    simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23579 (p : Pattern) (guard : d179493 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179492 p = 1 := by simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23578 p hg
    simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23580 (p : Pattern) (guard : d179494 p = 1) : d48329 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179493 p = 1 := by simpa only [d179494, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23579 p hg
    simpa only [d179494, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179494, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d179494, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23581 (p : Pattern) (guard : d179495 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179495, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23316 p hg
    simpa only [d179495, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179494 p = 1 := by simpa only [d179495, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23580 p hg
    simpa only [d179495, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23582 (p : Pattern) (guard : d179496 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179491 p = 1 := by simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23577 p hg
    simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23583 (p : Pattern) (guard : d179497 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179496 p = 1 := by simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23582 p hg
    simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23584 (p : Pattern) (guard : d179498 p = 1) : d48329 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179497 p = 1 := by simpa only [d179498, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23583 p hg
    simpa only [d179498, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179498, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d179498, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23585 (p : Pattern) (guard : d179499 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179499, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23316 p hg
    simpa only [d179499, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179498 p = 1 := by simpa only [d179499, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23584 p hg
    simpa only [d179499, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23586 (p : Pattern) (guard : d179500 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179495 p = 1 := by simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23581 p hg
    simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179499 p = 1 := by simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23585 p hg
    simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23587 (p : Pattern) (guard : d179501 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179500 p = 1 := by simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23586 p hg
    simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23588 (p : Pattern) (guard : d179502 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179501 p = 1 := by simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23587 p hg
    simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23589 (p : Pattern) (guard : d179503 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179502 p = 1 := by simpa only [d179503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23588 p hg
    simpa only [d179503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23590 (p : Pattern) (guard : d179504 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179499 p = 1 := by simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23585 p hg
    simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23591 (p : Pattern) (guard : d179505 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179504 p = 1 := by simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23590 p hg
    simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23592 (p : Pattern) (guard : d179506 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179505 p = 1 := by simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23591 p hg
    simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23593 (p : Pattern) (guard : d179507 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179506 p = 1 := by simpa only [d179507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23592 p hg
    simpa only [d179507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23594 (p : Pattern) (guard : d179508 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179503 p = 1 := by simpa only [d179508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23589 p hg
    simpa only [d179508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179507 p = 1 := by simpa only [d179508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23593 p hg
    simpa only [d179508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23595 (p : Pattern) (guard : d179509 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179508 p = 1 := by simpa only [d179509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23594 p hg
    simpa only [d179509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23596 (p : Pattern) (guard : d179510 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179509 p = 1 := by simpa only [d179510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23595 p hg
    simpa only [d179510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23597 (p : Pattern) (guard : d179511 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179510 p = 1 := by simpa only [d179511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23596 p hg
    simpa only [d179511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23598 (p : Pattern) (guard : d179512 p = 1) : d48330 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179511 p = 1 := by simpa only [d179512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23597 p hg
    simpa only [d179512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23599 (p : Pattern) (guard : d179516 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179502 p = 1 := by simpa only [d179516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23562 p hg
    simpa only [d179516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23600 (p : Pattern) (guard : d179517 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179506 p = 1 := by simpa only [d179517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23566 p hg
    simpa only [d179517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23601 (p : Pattern) (guard : d179518 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179516 p = 1 := by simpa only [d179518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23599 p hg
    simpa only [d179518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179517 p = 1 := by simpa only [d179518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23600 p hg
    simpa only [d179518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23602 (p : Pattern) (guard : d179519 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179518 p = 1 := by simpa only [d179519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23601 p hg
    simpa only [d179519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23603 (p : Pattern) (guard : d179520 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179519 p = 1 := by simpa only [d179520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23602 p hg
    simpa only [d179520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23604 (p : Pattern) (guard : d179521 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179520 p = 1 := by simpa only [d179521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23603 p hg
    simpa only [d179521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23605 (p : Pattern) (guard : d179522 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179521 p = 1 := by simpa only [d179522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23604 p hg
    simpa only [d179522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23606 (p : Pattern) (guard : d179523 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179512 p = 1 := by simpa only [d179523, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23598 p hg
    simpa only [d179523, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179522 p = 1 := by simpa only [d179523, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23605 p hg
    simpa only [d179523, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23607 (p : Pattern) (guard : d179524 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179513 p = 1 := by simpa only [d179524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23573 p hg
    simpa only [d179524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179523 p = 1 := by simpa only [d179524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23606 p hg
    simpa only [d179524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23608 (p : Pattern) (guard : d179525 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179524 p = 1 := by simpa only [d179525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23607 p hg
    simpa only [d179525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23284 p hg
    simpa only [d179525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23609 (p : Pattern) (guard : d180479 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179525 p = 1 := by simpa only [d180479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23608 p hg
    simpa only [d180479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23284 p hg
    simpa only [d180479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23610 (p : Pattern) (guard : d180480 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23284 p hg
    simpa only [d180480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180479 p = 1 := by simpa only [d180480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23609 p hg
    simpa only [d180480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23611 (p : Pattern) (guard : d179468 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare23612 (p : Pattern) (guard : d179469 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179468 p = 1 := by simpa only [d179469, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23611 p hg
    simpa only [d179469, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179469, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23352 p hg
    simpa only [d179469, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23613 (p : Pattern) (guard : d179470 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179469 p = 1 := by simpa only [d179470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23612 p hg
    simpa only [d179470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23614 (p : Pattern) (guard : d179471 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179470 p = 1 := by simpa only [d179471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23613 p hg
    simpa only [d179471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23615 (p : Pattern) (guard : d179480 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare23616 (p : Pattern) (guard : d179481 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179480 p = 1 := by simpa only [d179481, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23615 p hg
    simpa only [d179481, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179481, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23352 p hg
    simpa only [d179481, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23617 (p : Pattern) (guard : d179482 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179481 p = 1 := by simpa only [d179482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23616 p hg
    simpa only [d179482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23618 (p : Pattern) (guard : d179483 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179482 p = 1 := by simpa only [d179483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23617 p hg
    simpa only [d179483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23619 (p : Pattern) (guard : d179484 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179471 p = 1 := by simpa only [d179484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23614 p hg
    simpa only [d179484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179483 p = 1 := by simpa only [d179484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23618 p hg
    simpa only [d179484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23620 (p : Pattern) (guard : d179485 p = 1) : d48346 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179485, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23349 p hg
    simpa only [d179485, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179484 p = 1 := by simpa only [d179485, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23619 p hg
    simpa only [d179485, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23621 (p : Pattern) (guard : d179486 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179486, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23348 p hg
    simpa only [d179486, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179485 p = 1 := by simpa only [d179486, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23620 p hg
    simpa only [d179486, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23622 (p : Pattern) (guard : d179487 p = 1) : d48345 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179483 p = 1 := by simpa only [d179487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23618 p hg
    simpa only [d179487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23350 p hg
    simpa only [d179487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23623 (p : Pattern) (guard : d179488 p = 1) : d48346 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179488, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23349 p hg
    simpa only [d179488, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179487 p = 1 := by simpa only [d179488, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23622 p hg
    simpa only [d179488, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23624 (p : Pattern) (guard : d179489 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179489, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23348 p hg
    simpa only [d179489, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179488 p = 1 := by simpa only [d179489, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23623 p hg
    simpa only [d179489, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23625 (p : Pattern) (guard : d179490 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179486 p = 1 := by simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23621 p hg
    simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179489 p = 1 := by simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23624 p hg
    simpa only [d179490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23626 (p : Pattern) (guard : d179491 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179489 p = 1 := by simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23624 p hg
    simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d179491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23627 (p : Pattern) (guard : d179492 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179490 p = 1 := by simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23625 p hg
    simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179491 p = 1 := by simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23626 p hg
    simpa only [d179492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23628 (p : Pattern) (guard : d179493 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179492 p = 1 := by simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23627 p hg
    simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d179493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23629 (p : Pattern) (guard : d179494 p = 1) : d48356 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179493 p = 1 := by simpa only [d179494, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23628 p hg
    simpa only [d179494, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179494, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23363 p hg
    simpa only [d179494, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23630 (p : Pattern) (guard : d179495 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179495, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23347 p hg
    simpa only [d179495, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179494 p = 1 := by simpa only [d179495, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23629 p hg
    simpa only [d179495, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23631 (p : Pattern) (guard : d179496 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179491 p = 1 := by simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23626 p hg
    simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d179496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23632 (p : Pattern) (guard : d179497 p = 1) : d48354 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179496 p = 1 := by simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23631 p hg
    simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23359 p hg
    simpa only [d179497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23633 (p : Pattern) (guard : d179498 p = 1) : d48356 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179497 p = 1 := by simpa only [d179498, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23632 p hg
    simpa only [d179498, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179498, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23363 p hg
    simpa only [d179498, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23634 (p : Pattern) (guard : d179499 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179499, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23347 p hg
    simpa only [d179499, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179498 p = 1 := by simpa only [d179499, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23633 p hg
    simpa only [d179499, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23635 (p : Pattern) (guard : d179500 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179495 p = 1 := by simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23630 p hg
    simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179499 p = 1 := by simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23634 p hg
    simpa only [d179500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23636 (p : Pattern) (guard : d179501 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179500 p = 1 := by simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23635 p hg
    simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23637 (p : Pattern) (guard : d179502 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179501 p = 1 := by simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23636 p hg
    simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23638 (p : Pattern) (guard : d179516 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179502 p = 1 := by simpa only [d179516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23637 p hg
    simpa only [d179516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23639 (p : Pattern) (guard : d179504 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179499 p = 1 := by simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23634 p hg
    simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23640 (p : Pattern) (guard : d179505 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179504 p = 1 := by simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23639 p hg
    simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23641 (p : Pattern) (guard : d179506 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179505 p = 1 := by simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23640 p hg
    simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23642 (p : Pattern) (guard : d179517 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179506 p = 1 := by simpa only [d179517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23641 p hg
    simpa only [d179517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23643 (p : Pattern) (guard : d179518 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179516 p = 1 := by simpa only [d179518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23638 p hg
    simpa only [d179518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179517 p = 1 := by simpa only [d179518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23642 p hg
    simpa only [d179518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23644 (p : Pattern) (guard : d179519 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179518 p = 1 := by simpa only [d179519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23643 p hg
    simpa only [d179519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23645 (p : Pattern) (guard : d179520 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179519 p = 1 := by simpa only [d179520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23644 p hg
    simpa only [d179520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23646 (p : Pattern) (guard : d179521 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179520 p = 1 := by simpa only [d179521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23645 p hg
    simpa only [d179521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23647 (p : Pattern) (guard : d179522 p = 1) : d48357 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23346 p hg
    simpa only [d179522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179521 p = 1 := by simpa only [d179522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23646 p hg
    simpa only [d179522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23648 (p : Pattern) (guard : d180481 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180481, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180481, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179522 p = 1 := by simpa only [d180481, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23647 p hg
    simpa only [d180481, d48358, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23649 (p : Pattern) (guard : d180482 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180481 p = 1 := by simpa only [d180482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23648 p hg
    simpa only [d180482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23650 (p : Pattern) (guard : d180483 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180482 p = 1 := by simpa only [d180483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23649 p hg
    simpa only [d180483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23651 (p : Pattern) (guard : d180484 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180483 p = 1 := by simpa only [d180484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23650 p hg
    simpa only [d180484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23652 (p : Pattern) (guard : d180485 p = 1) : d48358 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d180484 p = 1 := by simpa only [d180485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23651 p hg
    simpa only [d180485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23345 p hg
    simpa only [d180485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23653 (p : Pattern) (guard : d180486 p = 1) : d48359 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d180480 p = 1 := by simpa only [d180486, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23610 p hg
    simpa only [d180486, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180485 p = 1 := by simpa only [d180486, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23652 p hg
    simpa only [d180486, d48359, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23654 (p : Pattern) (guard : d179637 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare23655 (p : Pattern) (guard : d179638 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179637 p = 1 := by simpa only [d179638, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23654 p hg
    simpa only [d179638, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179638, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23387 p hg
    simpa only [d179638, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23656 (p : Pattern) (guard : d179639 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d179639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179638 p = 1 := by simpa only [d179639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23655 p hg
    simpa only [d179639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23657 (p : Pattern) (guard : d179640 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179639 p = 1 := by simpa only [d179640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23656 p hg
    simpa only [d179640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d179640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23658 (p : Pattern) (guard : d179650 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare23659 (p : Pattern) (guard : d179651 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179650 p = 1 := by simpa only [d179651, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23658 p hg
    simpa only [d179651, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179651, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23387 p hg
    simpa only [d179651, d48361, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23660 (p : Pattern) (guard : d179652 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d179652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179651 p = 1 := by simpa only [d179652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23659 p hg
    simpa only [d179652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23661 (p : Pattern) (guard : d179653 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179652 p = 1 := by simpa only [d179653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23660 p hg
    simpa only [d179653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d179653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23662 (p : Pattern) (guard : d179654 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179640 p = 1 := by simpa only [d179654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23657 p hg
    simpa only [d179654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179653 p = 1 := by simpa only [d179654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23661 p hg
    simpa only [d179654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23663 (p : Pattern) (guard : d179655 p = 1) : d48362 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179655, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23384 p hg
    simpa only [d179655, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179654 p = 1 := by simpa only [d179655, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23662 p hg
    simpa only [d179655, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23664 (p : Pattern) (guard : d179656 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179656, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23383 p hg
    simpa only [d179656, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179655 p = 1 := by simpa only [d179656, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23663 p hg
    simpa only [d179656, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23665 (p : Pattern) (guard : d179657 p = 1) : d48361 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179653 p = 1 := by simpa only [d179657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23661 p hg
    simpa only [d179657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23385 p hg
    simpa only [d179657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23666 (p : Pattern) (guard : d179658 p = 1) : d48362 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179658, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23384 p hg
    simpa only [d179658, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179657 p = 1 := by simpa only [d179658, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23665 p hg
    simpa only [d179658, d48362, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23667 (p : Pattern) (guard : d179659 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179659, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23383 p hg
    simpa only [d179659, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179658 p = 1 := by simpa only [d179659, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23666 p hg
    simpa only [d179659, d48363, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23668 (p : Pattern) (guard : d179660 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179656 p = 1 := by simpa only [d179660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23664 p hg
    simpa only [d179660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179659 p = 1 := by simpa only [d179660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23667 p hg
    simpa only [d179660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23669 (p : Pattern) (guard : d179665 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179659 p = 1 := by simpa only [d179665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23667 p hg
    simpa only [d179665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d179665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23670 (p : Pattern) (guard : d179666 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179660 p = 1 := by simpa only [d179666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23668 p hg
    simpa only [d179666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179665 p = 1 := by simpa only [d179666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23669 p hg
    simpa only [d179666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23671 (p : Pattern) (guard : d179667 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179666 p = 1 := by simpa only [d179667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23670 p hg
    simpa only [d179667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d179667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23672 (p : Pattern) (guard : d179668 p = 1) : d48365 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179667 p = 1 := by simpa only [d179668, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23671 p hg
    simpa only [d179668, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179668, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23398 p hg
    simpa only [d179668, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23673 (p : Pattern) (guard : d179669 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179669, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d179669, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179668 p = 1 := by simpa only [d179669, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23672 p hg
    simpa only [d179669, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23674 (p : Pattern) (guard : d179674 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179665 p = 1 := by simpa only [d179674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23669 p hg
    simpa only [d179674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d179674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23675 (p : Pattern) (guard : d179675 p = 1) : d48363 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179674 p = 1 := by simpa only [d179675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23674 p hg
    simpa only [d179675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23394 p hg
    simpa only [d179675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23676 (p : Pattern) (guard : d179676 p = 1) : d48365 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179675 p = 1 := by simpa only [d179676, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23675 p hg
    simpa only [d179676, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179676, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23398 p hg
    simpa only [d179676, d48365, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23677 (p : Pattern) (guard : d179677 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179677, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d179677, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179676 p = 1 := by simpa only [d179677, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23676 p hg
    simpa only [d179677, d48366, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23678 (p : Pattern) (guard : d179678 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179669 p = 1 := by simpa only [d179678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23673 p hg
    simpa only [d179678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179677 p = 1 := by simpa only [d179678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23677 p hg
    simpa only [d179678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23679 (p : Pattern) (guard : d179679 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179678 p = 1 := by simpa only [d179679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23678 p hg
    simpa only [d179679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23680 (p : Pattern) (guard : d179680 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179679 p = 1 := by simpa only [d179680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23679 p hg
    simpa only [d179680, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179680, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179680, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23681 (p : Pattern) (guard : d179681 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179680 p = 1 := by simpa only [d179681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23680 p hg
    simpa only [d179681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23682 (p : Pattern) (guard : d179695 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179677 p = 1 := by simpa only [d179695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23677 p hg
    simpa only [d179695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23683 (p : Pattern) (guard : d179696 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179695 p = 1 := by simpa only [d179696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23682 p hg
    simpa only [d179696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23684 (p : Pattern) (guard : d179697 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179696 p = 1 := by simpa only [d179697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23683 p hg
    simpa only [d179697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23685 (p : Pattern) (guard : d179698 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179697 p = 1 := by simpa only [d179698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23684 p hg
    simpa only [d179698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d179698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23686 (p : Pattern) (guard : d180487 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179681 p = 1 := by simpa only [d180487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23681 p hg
    simpa only [d180487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179698 p = 1 := by simpa only [d180487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23685 p hg
    simpa only [d180487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23687 (p : Pattern) (guard : d180488 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180487 p = 1 := by simpa only [d180488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23686 p hg
    simpa only [d180488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23688 (p : Pattern) (guard : d180489 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d180488 p = 1 := by simpa only [d180489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23687 p hg
    simpa only [d180489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23689 (p : Pattern) (guard : d180490 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180489 p = 1 := by simpa only [d180490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23688 p hg
    simpa only [d180490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23690 (p : Pattern) (guard : d180491 p = 1) : d48366 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23382 p hg
    simpa only [d180491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180490 p = 1 := by simpa only [d180491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23689 p hg
    simpa only [d180491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23691 (p : Pattern) (guard : d180492 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180492, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d180492, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180491 p = 1 := by simpa only [d180492, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23690 p hg
    simpa only [d180492, d48367, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23692 (p : Pattern) (guard : d180493 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180492 p = 1 := by simpa only [d180493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23691 p hg
    simpa only [d180493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23693 (p : Pattern) (guard : d180494 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d180493 p = 1 := by simpa only [d180494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23692 p hg
    simpa only [d180494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23694 (p : Pattern) (guard : d180495 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d180494 p = 1 := by simpa only [d180495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23693 p hg
    simpa only [d180495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23695 (p : Pattern) (guard : d180496 p = 1) : d48367 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d180495 p = 1 := by simpa only [d180496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23694 p hg
    simpa only [d180496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23381 p hg
    simpa only [d180496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23696 (p : Pattern) (guard : d180497 p = 1) : d48387 p ≤ (0 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d180496 p = 1 := by simpa only [d180497, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23695 p hg
    simpa only [d180497, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d180497, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23415 p hg
    simpa only [d180497, d48387, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23697 (p : Pattern) (guard : d180498 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d180486 p = 1 := by simpa only [d180498, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23653 p hg
    simpa only [d180498, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180497 p = 1 := by simpa only [d180498, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23696 p hg
    simpa only [d180498, d48388, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23698 (p : Pattern) (guard : d180499 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180498 p = 1 := by simpa only [d180499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23697 p hg
    simpa only [d180499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23699 (p : Pattern) (guard : d180500 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180499 p = 1 := by simpa only [d180500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23698 p hg
    simpa only [d180500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23700 (p : Pattern) (guard : d180501 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180500 p = 1 := by simpa only [d180501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23699 p hg
    simpa only [d180501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23701 (p : Pattern) (guard : d180502 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180501 p = 1 := by simpa only [d180502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23700 p hg
    simpa only [d180502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23702 (p : Pattern) (guard : d180503 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180502 p = 1 := by simpa only [d180503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23701 p hg
    simpa only [d180503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23703 (p : Pattern) (guard : d180504 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180503 p = 1 := by simpa only [d180504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23702 p hg
    simpa only [d180504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23704 (p : Pattern) (guard : d180505 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180504 p = 1 := by simpa only [d180505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23703 p hg
    simpa only [d180505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23705 (p : Pattern) (guard : d180506 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d180506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23283 p hg
    simpa only [d180506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180505 p = 1 := by simpa only [d180506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23704 p hg
    simpa only [d180506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23706 (p : Pattern) (guard : d180507 p = 1) : d48388 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d180478 p = 1 := by simpa only [d180507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23535 p hg
    simpa only [d180507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d180506 p = 1 := by simpa only [d180507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23705 p hg
    simpa only [d180507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23707 (p : Pattern) (guard : d179726 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare23708 (p : Pattern) (guard : d179727 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179726 p = 1 := by simpa only [d179727, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23707 p hg
    simpa only [d179727, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179727, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23292 p hg
    simpa only [d179727, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23709 (p : Pattern) (guard : d179728 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179727 p = 1 := by simpa only [d179728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23708 p hg
    simpa only [d179728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23710 (p : Pattern) (guard : d179729 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179728 p = 1 := by simpa only [d179729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23709 p hg
    simpa only [d179729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23711 (p : Pattern) (guard : d179739 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare23712 (p : Pattern) (guard : d179740 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179739 p = 1 := by simpa only [d179740, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23711 p hg
    simpa only [d179740, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179740, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23292 p hg
    simpa only [d179740, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23713 (p : Pattern) (guard : d179741 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179740 p = 1 := by simpa only [d179741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23712 p hg
    simpa only [d179741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23714 (p : Pattern) (guard : d179742 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179741 p = 1 := by simpa only [d179742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23713 p hg
    simpa only [d179742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23715 (p : Pattern) (guard : d179743 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179729 p = 1 := by simpa only [d179743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23710 p hg
    simpa only [d179743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179742 p = 1 := by simpa only [d179743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23714 p hg
    simpa only [d179743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23716 (p : Pattern) (guard : d179744 p = 1) : d48326 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179744, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23289 p hg
    simpa only [d179744, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179743 p = 1 := by simpa only [d179744, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23715 p hg
    simpa only [d179744, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23717 (p : Pattern) (guard : d179745 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179745, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23288 p hg
    simpa only [d179745, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179744 p = 1 := by simpa only [d179745, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23716 p hg
    simpa only [d179745, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23718 (p : Pattern) (guard : d179746 p = 1) : d48313 p ≤ (0 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179742 p = 1 := by simpa only [d179746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23714 p hg
    simpa only [d179746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23290 p hg
    simpa only [d179746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23719 (p : Pattern) (guard : d179747 p = 1) : d48326 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179747, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23289 p hg
    simpa only [d179747, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179746 p = 1 := by simpa only [d179747, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23718 p hg
    simpa only [d179747, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23720 (p : Pattern) (guard : d179748 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179748, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23288 p hg
    simpa only [d179748, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179747 p = 1 := by simpa only [d179748, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23719 p hg
    simpa only [d179748, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23721 (p : Pattern) (guard : d179749 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179745 p = 1 := by simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23717 p hg
    simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179748 p = 1 := by simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23720 p hg
    simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23722 (p : Pattern) (guard : d179750 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179748 p = 1 := by simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23720 p hg
    simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23723 (p : Pattern) (guard : d179751 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179749 p = 1 := by simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23721 p hg
    simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179750 p = 1 := by simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23722 p hg
    simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23724 (p : Pattern) (guard : d179752 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179751 p = 1 := by simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23723 p hg
    simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23725 (p : Pattern) (guard : d179753 p = 1) : d48338 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179752 p = 1 := by simpa only [d179753, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23724 p hg
    simpa only [d179753, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179753, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d179753, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23726 (p : Pattern) (guard : d179754 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179754, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d179754, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179753 p = 1 := by simpa only [d179754, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23725 p hg
    simpa only [d179754, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23727 (p : Pattern) (guard : d179755 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179750 p = 1 := by simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23722 p hg
    simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23728 (p : Pattern) (guard : d179756 p = 1) : d48337 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179755 p = 1 := by simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23727 p hg
    simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23299 p hg
    simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23729 (p : Pattern) (guard : d179757 p = 1) : d48338 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179756 p = 1 := by simpa only [d179757, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23728 p hg
    simpa only [d179757, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179757, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23303 p hg
    simpa only [d179757, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23730 (p : Pattern) (guard : d179758 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179758, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23287 p hg
    simpa only [d179758, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179757 p = 1 := by simpa only [d179758, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23729 p hg
    simpa only [d179758, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23731 (p : Pattern) (guard : d179759 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179754 p = 1 := by simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23726 p hg
    simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179758 p = 1 := by simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23730 p hg
    simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23732 (p : Pattern) (guard : d179760 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179759 p = 1 := by simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23731 p hg
    simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23733 (p : Pattern) (guard : d179761 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179760 p = 1 := by simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23732 p hg
    simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23734 (p : Pattern) (guard : d179762 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179761 p = 1 := by simpa only [d179762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23733 p hg
    simpa only [d179762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23735 (p : Pattern) (guard : d179763 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179758 p = 1 := by simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23730 p hg
    simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23736 (p : Pattern) (guard : d179764 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179763 p = 1 := by simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23735 p hg
    simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23737 (p : Pattern) (guard : d179765 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179764 p = 1 := by simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23736 p hg
    simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23738 (p : Pattern) (guard : d179766 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179765 p = 1 := by simpa only [d179766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23737 p hg
    simpa only [d179766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23739 (p : Pattern) (guard : d179767 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179762 p = 1 := by simpa only [d179767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23734 p hg
    simpa only [d179767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179766 p = 1 := by simpa only [d179767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23738 p hg
    simpa only [d179767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23740 (p : Pattern) (guard : d179768 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179767 p = 1 := by simpa only [d179768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23739 p hg
    simpa only [d179768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23741 (p : Pattern) (guard : d179769 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179768 p = 1 := by simpa only [d179769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23740 p hg
    simpa only [d179769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23742 (p : Pattern) (guard : d179770 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179769 p = 1 := by simpa only [d179770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23741 p hg
    simpa only [d179770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23743 (p : Pattern) (guard : d179771 p = 1) : d48339 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23286 p hg
    simpa only [d179771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179770 p = 1 := by simpa only [d179771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23742 p hg
    simpa only [d179771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23744 (p : Pattern) (guard : d179772 p = 1) : d48340 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179772, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23285 p hg
    simpa only [d179772, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179771 p = 1 := by simpa only [d179772, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23743 p hg
    simpa only [d179772, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23745 (p : Pattern) (guard : d179745 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179745, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23317 p hg
    simpa only [d179745, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179744 p = 1 := by simpa only [d179745, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23716 p hg
    simpa only [d179745, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23746 (p : Pattern) (guard : d179748 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179748, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23317 p hg
    simpa only [d179748, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179747 p = 1 := by simpa only [d179748, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23719 p hg
    simpa only [d179748, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23747 (p : Pattern) (guard : d179749 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179745 p = 1 := by simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23745 p hg
    simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179748 p = 1 := by simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23746 p hg
    simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23748 (p : Pattern) (guard : d179750 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179748 p = 1 := by simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23746 p hg
    simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23319 p hg
    simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare23749 (p : Pattern) (guard : d179751 p = 1) : d48327 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179749 p = 1 := by simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23747 p hg
    simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179750 p = 1 := by simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23748 p hg
    simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
