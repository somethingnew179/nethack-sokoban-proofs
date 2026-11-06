import NetHack.Soko22Hazard87.Compare013
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare3500 (p : Pattern) (guard : d475 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3455 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3501 (p : Pattern) (guard : d476 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d328 p = 1 := by simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3499 p hg
    simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3500 p hg
    simpa only [d476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3502 (p : Pattern) (guard : d477 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d476 p = 1 := by simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3501 p hg
    simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d477, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3503 (p : Pattern) (guard : d478 p = 1) : d47699 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d477 p = 1 := by simpa only [d478, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3502 p hg
    simpa only [d478, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d478, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3414 p hg
    simpa only [d478, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3504 (p : Pattern) (guard : d479 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d479, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d479, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d478 p = 1 := by simpa only [d479, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3503 p hg
    simpa only [d479, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3505 (p : Pattern) (guard : d480 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3500 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3506 (p : Pattern) (guard : d481 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3505 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3507 (p : Pattern) (guard : d482 p = 1) : d47699 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3506 p hg
    simpa only [d482, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3414 p hg
    simpa only [d482, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3508 (p : Pattern) (guard : d483 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d483, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3507 p hg
    simpa only [d483, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3509 (p : Pattern) (guard : d484 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d479 p = 1 := by simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3504 p hg
    simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3508 p hg
    simpa only [d484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3510 (p : Pattern) (guard : d485 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d484 p = 1 := by simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3509 p hg
    simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3511 (p : Pattern) (guard : d486 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d485 p = 1 := by simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3510 p hg
    simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3512 (p : Pattern) (guard : d487 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d486 p = 1 := by simpa only [d487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3511 p hg
    simpa only [d487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3513 (p : Pattern) (guard : d488 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3508 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3514 (p : Pattern) (guard : d489 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3513 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3515 (p : Pattern) (guard : d490 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3514 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3516 (p : Pattern) (guard : d491 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d490 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3515 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3517 (p : Pattern) (guard : d492 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d487 p = 1 := by simpa only [d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3512 p hg
    simpa only [d492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d491 p = 1 := by simpa only [d492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3516 p hg
    simpa only [d492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3518 (p : Pattern) (guard : d493 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d492 p = 1 := by simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3517 p hg
    simpa only [d493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3519 (p : Pattern) (guard : d494 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d493 p = 1 := by simpa only [d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3518 p hg
    simpa only [d494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3520 (p : Pattern) (guard : d495 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d494 p = 1 := by simpa only [d495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3519 p hg
    simpa only [d495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3521 (p : Pattern) (guard : d496 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d495 p = 1 := by simpa only [d496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3520 p hg
    simpa only [d496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3522 (p : Pattern) (guard : d497 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d497, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d497, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d496 p = 1 := by simpa only [d497, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3521 p hg
    simpa only [d497, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3523 (p : Pattern) (guard : d500 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d486 p = 1 := by simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3511 p hg
    simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3524 (p : Pattern) (guard : d501 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d490 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3515 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3525 (p : Pattern) (guard : d502 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d500 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3523 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d501 p = 1 := by simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3524 p hg
    simpa only [d502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3526 (p : Pattern) (guard : d503 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d502 p = 1 := by simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3525 p hg
    simpa only [d503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3527 (p : Pattern) (guard : d504 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d503 p = 1 := by simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3526 p hg
    simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3528 (p : Pattern) (guard : d505 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d504 p = 1 := by simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3527 p hg
    simpa only [d505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3529 (p : Pattern) (guard : d506 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d505 p = 1 := by simpa only [d506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3528 p hg
    simpa only [d506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3530 (p : Pattern) (guard : d53680 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53680, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d53680, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d506 p = 1 := by simpa only [d53680, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3529 p hg
    simpa only [d53680, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3531 (p : Pattern) (guard : d65966 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d497 p = 1 := by simpa only [d65966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3522 p hg
    simpa only [d65966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53680 p = 1 := by simpa only [d65966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3530 p hg
    simpa only [d65966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3532 (p : Pattern) (guard : d65967 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d65966 p = 1 := by simpa only [d65967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3531 p hg
    simpa only [d65967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d65967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3533 (p : Pattern) (guard : d65968 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d65967 p = 1 := by simpa only [d65968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3532 p hg
    simpa only [d65968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d65968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3534 (p : Pattern) (guard : d65969 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d65969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65968 p = 1 := by simpa only [d65969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3533 p hg
    simpa only [d65969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3535 (p : Pattern) (guard : d65970 p = 1) : d47768 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d65969 p = 1 := by simpa only [d65970, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3534 p hg
    simpa only [d65970, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65970, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3438 p hg
    simpa only [d65970, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3536 (p : Pattern) (guard : d65971 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d65970 p = 1 := by simpa only [d65971, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3535 p hg
    simpa only [d65971, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65971, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3440 p hg
    simpa only [d65971, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3537 (p : Pattern) (guard : d65972 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65971 p = 1 := by simpa only [d65972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3536 p hg
    simpa only [d65972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3538 (p : Pattern) (guard : d65973 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65972 p = 1 := by simpa only [d65973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3537 p hg
    simpa only [d65973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3539 (p : Pattern) (guard : d65974 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65973 p = 1 := by simpa only [d65974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3538 p hg
    simpa only [d65974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3540 (p : Pattern) (guard : d65975 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65974 p = 1 := by simpa only [d65975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3539 p hg
    simpa only [d65975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3541 (p : Pattern) (guard : d65976 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65975 p = 1 := by simpa only [d65976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3540 p hg
    simpa only [d65976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3542 (p : Pattern) (guard : d65977 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65976 p = 1 := by simpa only [d65977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3541 p hg
    simpa only [d65977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3543 (p : Pattern) (guard : d65978 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d65965 p = 1 := by simpa only [d65978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3489 p hg
    simpa only [d65978, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65977 p = 1 := by simpa only [d65978, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3542 p hg
    simpa only [d65978, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3544 (p : Pattern) (guard : d543 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1377 p hg
    simpa only [d543, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d543, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3545 (p : Pattern) (guard : d544 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d543 p = 1 := by simpa only [d544, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3544 p hg
    simpa only [d544, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d544, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d544, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3546 (p : Pattern) (guard : d545 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d545, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d545, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d545, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3545 p hg
    simpa only [d545, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3547 (p : Pattern) (guard : d546 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3546 p hg
    simpa only [d546, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d546, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3548 (p : Pattern) (guard : d547 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3547 p hg
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d322 p = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3493 p hg
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3549 (p : Pattern) (guard : d751 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1385 p hg
    simpa only [d751, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d751, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3550 (p : Pattern) (guard : d752 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d751 p = 1 := by simpa only [d752, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3549 p hg
    simpa only [d752, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d752, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d752, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3551 (p : Pattern) (guard : d753 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d753, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3550 p hg
    simpa only [d753, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3552 (p : Pattern) (guard : d754 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3551 p hg
    simpa only [d754, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d754, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3553 (p : Pattern) (guard : d755 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3493 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3552 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3554 (p : Pattern) (guard : d756 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d547 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3548 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d755 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3553 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3555 (p : Pattern) (guard : d757 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3552 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3556 (p : Pattern) (guard : d758 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3553 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3555 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3557 (p : Pattern) (guard : d759 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d756 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3554 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3556 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3558 (p : Pattern) (guard : d760 p = 1) : d47686 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d760, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3395 p hg
    simpa only [d760, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d759 p = 1 := by simpa only [d760, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3557 p hg
    simpa only [d760, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3559 (p : Pattern) (guard : d761 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d761, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3394 p hg
    simpa only [d761, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d760 p = 1 := by simpa only [d761, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3558 p hg
    simpa only [d761, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3560 (p : Pattern) (guard : d762 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3555 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3561 (p : Pattern) (guard : d763 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3556 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3560 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3562 (p : Pattern) (guard : d764 p = 1) : d47686 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d764, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3395 p hg
    simpa only [d764, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d763 p = 1 := by simpa only [d764, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3561 p hg
    simpa only [d764, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3563 (p : Pattern) (guard : d765 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3394 p hg
    simpa only [d765, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3562 p hg
    simpa only [d765, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3564 (p : Pattern) (guard : d766 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d761 p = 1 := by simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3559 p hg
    simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3563 p hg
    simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3565 (p : Pattern) (guard : d767 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3563 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3566 (p : Pattern) (guard : d768 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d766 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3564 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3565 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3567 (p : Pattern) (guard : d769 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3566 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3568 (p : Pattern) (guard : d770 p = 1) : d47699 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d770, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3567 p hg
    simpa only [d770, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3414 p hg
    simpa only [d770, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3569 (p : Pattern) (guard : d771 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d771, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d771, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d771, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3568 p hg
    simpa only [d771, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3570 (p : Pattern) (guard : d772 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3565 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3571 (p : Pattern) (guard : d773 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3570 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3572 (p : Pattern) (guard : d774 p = 1) : d47699 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3571 p hg
    simpa only [d774, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3414 p hg
    simpa only [d774, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3573 (p : Pattern) (guard : d775 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d775, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3572 p hg
    simpa only [d775, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3574 (p : Pattern) (guard : d776 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d771 p = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3569 p hg
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3573 p hg
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3575 (p : Pattern) (guard : d777 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d776 p = 1 := by simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3574 p hg
    simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3576 (p : Pattern) (guard : d778 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d777 p = 1 := by simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3575 p hg
    simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3577 (p : Pattern) (guard : d779 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d778 p = 1 := by simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3576 p hg
    simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3578 (p : Pattern) (guard : d780 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3573 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3579 (p : Pattern) (guard : d781 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3578 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3580 (p : Pattern) (guard : d782 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3579 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3581 (p : Pattern) (guard : d783 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d782 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3580 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3582 (p : Pattern) (guard : d784 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d779 p = 1 := by simpa only [d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3577 p hg
    simpa only [d784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d783 p = 1 := by simpa only [d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3581 p hg
    simpa only [d784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3583 (p : Pattern) (guard : d785 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d784 p = 1 := by simpa only [d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3582 p hg
    simpa only [d785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3584 (p : Pattern) (guard : d786 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d785 p = 1 := by simpa only [d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3583 p hg
    simpa only [d786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3585 (p : Pattern) (guard : d787 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d786 p = 1 := by simpa only [d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3584 p hg
    simpa only [d787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3586 (p : Pattern) (guard : d788 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d787 p = 1 := by simpa only [d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3585 p hg
    simpa only [d788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3587 (p : Pattern) (guard : d789 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d789, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d789, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d788 p = 1 := by simpa only [d789, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3586 p hg
    simpa only [d789, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3588 (p : Pattern) (guard : d792 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d778 p = 1 := by simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3576 p hg
    simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3589 (p : Pattern) (guard : d793 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d782 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3580 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3590 (p : Pattern) (guard : d794 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d792 p = 1 := by simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3588 p hg
    simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3589 p hg
    simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3591 (p : Pattern) (guard : d795 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3590 p hg
    simpa only [d795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3592 (p : Pattern) (guard : d796 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d795 p = 1 := by simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3591 p hg
    simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3593 (p : Pattern) (guard : d797 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d796 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3592 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3594 (p : Pattern) (guard : d798 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d797 p = 1 := by simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3593 p hg
    simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3595 (p : Pattern) (guard : d53707 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53707, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d53707, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d53707, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3594 p hg
    simpa only [d53707, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3596 (p : Pattern) (guard : d65979 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d789 p = 1 := by simpa only [d65979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3587 p hg
    simpa only [d65979, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53707 p = 1 := by simpa only [d65979, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3595 p hg
    simpa only [d65979, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3597 (p : Pattern) (guard : d65980 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d65979 p = 1 := by simpa only [d65980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3596 p hg
    simpa only [d65980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d65980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3598 (p : Pattern) (guard : d65981 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d65980 p = 1 := by simpa only [d65981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3597 p hg
    simpa only [d65981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d65981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3599 (p : Pattern) (guard : d65982 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d65982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65981 p = 1 := by simpa only [d65982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3598 p hg
    simpa only [d65982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3600 (p : Pattern) (guard : d65983 p = 1) : d47768 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d65982 p = 1 := by simpa only [d65983, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3599 p hg
    simpa only [d65983, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65983, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3438 p hg
    simpa only [d65983, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3601 (p : Pattern) (guard : d65984 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d65983 p = 1 := by simpa only [d65984, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3600 p hg
    simpa only [d65984, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65984, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3440 p hg
    simpa only [d65984, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3602 (p : Pattern) (guard : d65985 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65984 p = 1 := by simpa only [d65985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3601 p hg
    simpa only [d65985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3603 (p : Pattern) (guard : d65986 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65985 p = 1 := by simpa only [d65986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3602 p hg
    simpa only [d65986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3604 (p : Pattern) (guard : d65987 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65986 p = 1 := by simpa only [d65987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3603 p hg
    simpa only [d65987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3605 (p : Pattern) (guard : d65988 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65987 p = 1 := by simpa only [d65988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3604 p hg
    simpa only [d65988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3606 (p : Pattern) (guard : d65989 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65988 p = 1 := by simpa only [d65989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3605 p hg
    simpa only [d65989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3607 (p : Pattern) (guard : d65990 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65989 p = 1 := by simpa only [d65990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3606 p hg
    simpa only [d65990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3608 (p : Pattern) (guard : d65991 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65990 p = 1 := by simpa only [d65991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3607 p hg
    simpa only [d65991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3609 (p : Pattern) (guard : d65992 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d65978 p = 1 := by simpa only [d65992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3543 p hg
    simpa only [d65992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65991 p = 1 := by simpa only [d65992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3608 p hg
    simpa only [d65992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3610 (p : Pattern) (guard : d1100 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1493 p hg
    simpa only [d1100, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d1100, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3611 (p : Pattern) (guard : d1101 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1100 p = 1 := by simpa only [d1101, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3610 p hg
    simpa only [d1101, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1101, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1101, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3612 (p : Pattern) (guard : d1102 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1102, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d1102, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1102, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3611 p hg
    simpa only [d1102, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3613 (p : Pattern) (guard : d1103 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3612 p hg
    simpa only [d1103, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d1103, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3614 (p : Pattern) (guard : d1110 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1510 p hg
    simpa only [d1110, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d1110, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3615 (p : Pattern) (guard : d1111 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1110 p = 1 := by simpa only [d1111, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3614 p hg
    simpa only [d1111, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1111, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1111, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3616 (p : Pattern) (guard : d1112 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d1112, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3615 p hg
    simpa only [d1112, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3617 (p : Pattern) (guard : d1113 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3616 p hg
    simpa only [d1113, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d1113, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3618 (p : Pattern) (guard : d1114 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3613 p hg
    simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1113 p = 1 := by simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3617 p hg
    simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3619 (p : Pattern) (guard : d1121 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1528 p hg
    simpa only [d1121, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d1121, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3620 (p : Pattern) (guard : d1122 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1121 p = 1 := by simpa only [d1122, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3619 p hg
    simpa only [d1122, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1122, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3621 (p : Pattern) (guard : d1123 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d1123, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3620 p hg
    simpa only [d1123, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3622 (p : Pattern) (guard : d1124 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3621 p hg
    simpa only [d1124, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d1124, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3623 (p : Pattern) (guard : d1125 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3617 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3622 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3624 (p : Pattern) (guard : d1126 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1114 p = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3618 p hg
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3625 (p : Pattern) (guard : d1127 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3622 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3626 (p : Pattern) (guard : d1128 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3623 p hg
    simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1127 p = 1 := by simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3625 p hg
    simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3627 (p : Pattern) (guard : d1129 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3624 p hg
    simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1128 p = 1 := by simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3626 p hg
    simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3628 (p : Pattern) (guard : d1130 p = 1) : d47686 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1130, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3395 p hg
    simpa only [d1130, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1129 p = 1 := by simpa only [d1130, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3627 p hg
    simpa only [d1130, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3629 (p : Pattern) (guard : d1131 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1131, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3394 p hg
    simpa only [d1131, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1130 p = 1 := by simpa only [d1131, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3628 p hg
    simpa only [d1131, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3630 (p : Pattern) (guard : d1136 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1135 p = 1 := by simpa only [d1136, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1548 p hg
    simpa only [d1136, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1136, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d1136, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3631 (p : Pattern) (guard : d1137 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1136 p = 1 := by simpa only [d1137, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3630 p hg
    simpa only [d1137, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1137, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1137, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3632 (p : Pattern) (guard : d1138 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1138, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d1138, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1137 p = 1 := by simpa only [d1138, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3631 p hg
    simpa only [d1138, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3633 (p : Pattern) (guard : d1139 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1138 p = 1 := by simpa only [d1139, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3632 p hg
    simpa only [d1139, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1139, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d1139, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3634 (p : Pattern) (guard : d1140 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1139 p = 1 := by simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3633 p hg
    simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3635 (p : Pattern) (guard : d1141 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3625 p hg
    simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1140 p = 1 := by simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3634 p hg
    simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3636 (p : Pattern) (guard : d1142 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1128 p = 1 := by simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3626 p hg
    simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1141 p = 1 := by simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3635 p hg
    simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3637 (p : Pattern) (guard : d1143 p = 1) : d47686 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1143, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3395 p hg
    simpa only [d1143, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1142 p = 1 := by simpa only [d1143, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3636 p hg
    simpa only [d1143, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3638 (p : Pattern) (guard : d1144 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1144, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3394 p hg
    simpa only [d1144, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1143 p = 1 := by simpa only [d1144, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3637 p hg
    simpa only [d1144, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3639 (p : Pattern) (guard : d1145 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1131 p = 1 := by simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3629 p hg
    simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1144 p = 1 := by simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3638 p hg
    simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3640 (p : Pattern) (guard : d1146 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1144 p = 1 := by simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3638 p hg
    simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3641 (p : Pattern) (guard : d1147 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1145 p = 1 := by simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3639 p hg
    simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1146 p = 1 := by simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3640 p hg
    simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3642 (p : Pattern) (guard : d1148 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1147 p = 1 := by simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3641 p hg
    simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3643 (p : Pattern) (guard : d1149 p = 1) : d47699 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d1149, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3642 p hg
    simpa only [d1149, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1149, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3414 p hg
    simpa only [d1149, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3644 (p : Pattern) (guard : d1150 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d1150, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1149 p = 1 := by simpa only [d1150, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3643 p hg
    simpa only [d1150, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3645 (p : Pattern) (guard : d1151 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1146 p = 1 := by simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3640 p hg
    simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3646 (p : Pattern) (guard : d1152 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3645 p hg
    simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3647 (p : Pattern) (guard : d1153 p = 1) : d47699 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1152 p = 1 := by simpa only [d1153, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3646 p hg
    simpa only [d1153, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1153, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3414 p hg
    simpa only [d1153, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3648 (p : Pattern) (guard : d1154 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1154, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d1154, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1153 p = 1 := by simpa only [d1154, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3647 p hg
    simpa only [d1154, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3649 (p : Pattern) (guard : d1155 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3644 p hg
    simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1154 p = 1 := by simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3648 p hg
    simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3650 (p : Pattern) (guard : d1156 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1155 p = 1 := by simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3649 p hg
    simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3651 (p : Pattern) (guard : d1157 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1156 p = 1 := by simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3650 p hg
    simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3652 (p : Pattern) (guard : d1158 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1157 p = 1 := by simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3651 p hg
    simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3653 (p : Pattern) (guard : d1159 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1154 p = 1 := by simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3648 p hg
    simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3654 (p : Pattern) (guard : d1160 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1159 p = 1 := by simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3653 p hg
    simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3655 (p : Pattern) (guard : d1161 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1160 p = 1 := by simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3654 p hg
    simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3656 (p : Pattern) (guard : d1162 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1161 p = 1 := by simpa only [d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3655 p hg
    simpa only [d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3657 (p : Pattern) (guard : d1163 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3652 p hg
    simpa only [d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1162 p = 1 := by simpa only [d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3656 p hg
    simpa only [d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3658 (p : Pattern) (guard : d1164 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1163 p = 1 := by simpa only [d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3657 p hg
    simpa only [d1164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3659 (p : Pattern) (guard : d1165 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1164 p = 1 := by simpa only [d1165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3658 p hg
    simpa only [d1165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3660 (p : Pattern) (guard : d1166 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1165 p = 1 := by simpa only [d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3659 p hg
    simpa only [d1166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3661 (p : Pattern) (guard : d1167 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1166 p = 1 := by simpa only [d1167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3660 p hg
    simpa only [d1167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3662 (p : Pattern) (guard : d1168 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1168, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d1168, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d1168, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3661 p hg
    simpa only [d1168, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3663 (p : Pattern) (guard : d1171 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1157 p = 1 := by simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3651 p hg
    simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3664 (p : Pattern) (guard : d1172 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1161 p = 1 := by simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3655 p hg
    simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3665 (p : Pattern) (guard : d1173 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3663 p hg
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1172 p = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3664 p hg
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3666 (p : Pattern) (guard : d1174 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3665 p hg
    simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3667 (p : Pattern) (guard : d1175 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d1175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3666 p hg
    simpa only [d1175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3668 (p : Pattern) (guard : d1176 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3667 p hg
    simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3669 (p : Pattern) (guard : d1177 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3668 p hg
    simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3670 (p : Pattern) (guard : d53735 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53735, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d53735, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1177 p = 1 := by simpa only [d53735, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3669 p hg
    simpa only [d53735, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3671 (p : Pattern) (guard : d65993 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d1168 p = 1 := by simpa only [d65993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3662 p hg
    simpa only [d65993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53735 p = 1 := by simpa only [d65993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3670 p hg
    simpa only [d65993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3672 (p : Pattern) (guard : d65994 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d65993 p = 1 := by simpa only [d65994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3671 p hg
    simpa only [d65994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d65994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3673 (p : Pattern) (guard : d65995 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d65994 p = 1 := by simpa only [d65995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3672 p hg
    simpa only [d65995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d65995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3674 (p : Pattern) (guard : d65996 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d65996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65995 p = 1 := by simpa only [d65996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3673 p hg
    simpa only [d65996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3675 (p : Pattern) (guard : d65997 p = 1) : d47768 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d65996 p = 1 := by simpa only [d65997, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3674 p hg
    simpa only [d65997, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65997, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3438 p hg
    simpa only [d65997, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3676 (p : Pattern) (guard : d65998 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 48 with
  | false =>
    have hg : d65997 p = 1 := by simpa only [d65998, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3675 p hg
    simpa only [d65998, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d65998, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3440 p hg
    simpa only [d65998, d47911, d65730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3677 (p : Pattern) (guard : d65999 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d65999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d65999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65998 p = 1 := by simpa only [d65999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3676 p hg
    simpa only [d65999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3678 (p : Pattern) (guard : d66000 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d65999 p = 1 := by simpa only [d66000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3677 p hg
    simpa only [d66000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3679 (p : Pattern) (guard : d66001 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66000 p = 1 := by simpa only [d66001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3678 p hg
    simpa only [d66001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3680 (p : Pattern) (guard : d66002 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66001 p = 1 := by simpa only [d66002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3679 p hg
    simpa only [d66002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3681 (p : Pattern) (guard : d66003 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66002 p = 1 := by simpa only [d66003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3680 p hg
    simpa only [d66003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3682 (p : Pattern) (guard : d66004 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66003 p = 1 := by simpa only [d66004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3681 p hg
    simpa only [d66004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3683 (p : Pattern) (guard : d66005 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66004 p = 1 := by simpa only [d66005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3682 p hg
    simpa only [d66005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3684 (p : Pattern) (guard : d66006 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3391 p hg
    simpa only [d66006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66005 p = 1 := by simpa only [d66006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3683 p hg
    simpa only [d66006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3685 (p : Pattern) (guard : d66007 p = 1) : d47911 p ≤ (-1 : Int) + d65730 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d65992 p = 1 := by simpa only [d66007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3609 p hg
    simpa only [d66007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d66006 p = 1 := by simpa only [d66007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3684 p hg
    simpa only [d66007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3686 (p : Pattern) (guard : d1555 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1554 p = 1 := by simpa only [d1555, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1683 p hg
    simpa only [d1555, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1555, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d1555, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3687 (p : Pattern) (guard : d1556 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1555 p = 1 := by simpa only [d1556, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3686 p hg
    simpa only [d1556, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1556, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1556, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3688 (p : Pattern) (guard : d1557 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1557, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d1557, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1557, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3687 p hg
    simpa only [d1557, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3689 (p : Pattern) (guard : d1558 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3688 p hg
    simpa only [d1558, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d1558, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3690 (p : Pattern) (guard : d1570 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1569 p = 1 := by simpa only [d1570, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1710 p hg
    simpa only [d1570, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1570, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d1570, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3691 (p : Pattern) (guard : d1571 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1570 p = 1 := by simpa only [d1571, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3690 p hg
    simpa only [d1571, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1571, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1571, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3692 (p : Pattern) (guard : d1572 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d1572, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3691 p hg
    simpa only [d1572, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3693 (p : Pattern) (guard : d1573 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3692 p hg
    simpa only [d1573, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d1573, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3694 (p : Pattern) (guard : d1574 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1558 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3689 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1573 p = 1 := by simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3693 p hg
    simpa only [d1574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3695 (p : Pattern) (guard : d1582 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1730 p hg
    simpa only [d1582, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d1582, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3696 (p : Pattern) (guard : d1583 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1582 p = 1 := by simpa only [d1583, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3695 p hg
    simpa only [d1583, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1583, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1583, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3697 (p : Pattern) (guard : d1584 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d1584, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3696 p hg
    simpa only [d1584, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3698 (p : Pattern) (guard : d1585 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3697 p hg
    simpa only [d1585, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d1585, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3699 (p : Pattern) (guard : d1586 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1573 p = 1 := by simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3693 p hg
    simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1585 p = 1 := by simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3698 p hg
    simpa only [d1586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3700 (p : Pattern) (guard : d1587 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1574 p = 1 := by simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3694 p hg
    simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1586 p = 1 := by simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3699 p hg
    simpa only [d1587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3701 (p : Pattern) (guard : d1588 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1585 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3698 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d1588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3702 (p : Pattern) (guard : d1589 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1586 p = 1 := by simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3699 p hg
    simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1588 p = 1 := by simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3701 p hg
    simpa only [d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3703 (p : Pattern) (guard : d1590 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1587 p = 1 := by simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3700 p hg
    simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1589 p = 1 := by simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3702 p hg
    simpa only [d1590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3704 (p : Pattern) (guard : d1591 p = 1) : d47686 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1591, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3395 p hg
    simpa only [d1591, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1590 p = 1 := by simpa only [d1591, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3703 p hg
    simpa only [d1591, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3705 (p : Pattern) (guard : d1592 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1592, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3394 p hg
    simpa only [d1592, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1591 p = 1 := by simpa only [d1592, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3704 p hg
    simpa only [d1592, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3706 (p : Pattern) (guard : d1597 p = 1) : d47660 p ≤ (-1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1596 p = 1 := by simpa only [d1597, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1750 p hg
    simpa only [d1597, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1597, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3397 p hg
    simpa only [d1597, d47660, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3707 (p : Pattern) (guard : d1598 p = 1) : d47663 p ≤ (-1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1597 p = 1 := by simpa only [d1598, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3706 p hg
    simpa only [d1598, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1598, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1598, d47663, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3708 (p : Pattern) (guard : d1599 p = 1) : d47664 p ≤ (-1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1599, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3396 p hg
    simpa only [d1599, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1598 p = 1 := by simpa only [d1599, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3707 p hg
    simpa only [d1599, d47664, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3709 (p : Pattern) (guard : d1600 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1599 p = 1 := by simpa only [d1600, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3708 p hg
    simpa only [d1600, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1600, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3402 p hg
    simpa only [d1600, d47685, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3710 (p : Pattern) (guard : d1601 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1600 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3709 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d1601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3711 (p : Pattern) (guard : d1602 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1588 p = 1 := by simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3701 p hg
    simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1601 p = 1 := by simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3710 p hg
    simpa only [d1602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3712 (p : Pattern) (guard : d1603 p = 1) : d47685 p ≤ (-1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1589 p = 1 := by simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3702 p hg
    simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1602 p = 1 := by simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3711 p hg
    simpa only [d1603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3713 (p : Pattern) (guard : d1604 p = 1) : d47686 p ≤ (-1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1604, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3395 p hg
    simpa only [d1604, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1603 p = 1 := by simpa only [d1604, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3712 p hg
    simpa only [d1604, d47686, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3714 (p : Pattern) (guard : d1605 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1605, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3394 p hg
    simpa only [d1605, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1604 p = 1 := by simpa only [d1605, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3713 p hg
    simpa only [d1605, d47687, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3715 (p : Pattern) (guard : d1606 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1592 p = 1 := by simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3705 p hg
    simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1605 p = 1 := by simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3714 p hg
    simpa only [d1606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3716 (p : Pattern) (guard : d1607 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1605 p = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3714 p hg
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d1607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3717 (p : Pattern) (guard : d1608 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1606 p = 1 := by simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3715 p hg
    simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1607 p = 1 := by simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3716 p hg
    simpa only [d1608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3718 (p : Pattern) (guard : d1609 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1608 p = 1 := by simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3717 p hg
    simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d1609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3719 (p : Pattern) (guard : d1610 p = 1) : d47699 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1609 p = 1 := by simpa only [d1610, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3718 p hg
    simpa only [d1610, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1610, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3414 p hg
    simpa only [d1610, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3720 (p : Pattern) (guard : d1611 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1611, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d1611, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1610 p = 1 := by simpa only [d1611, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3719 p hg
    simpa only [d1611, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3721 (p : Pattern) (guard : d1612 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1607 p = 1 := by simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3716 p hg
    simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d1612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3722 (p : Pattern) (guard : d1613 p = 1) : d47687 p ≤ (-1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1612 p = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3721 p hg
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d1613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3723 (p : Pattern) (guard : d1614 p = 1) : d47699 p ≤ (-1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1613 p = 1 := by simpa only [d1614, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3722 p hg
    simpa only [d1614, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1614, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3414 p hg
    simpa only [d1614, d47699, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3724 (p : Pattern) (guard : d1615 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1615, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1133 p hg
    simpa only [d1615, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1614 p = 1 := by simpa only [d1615, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3723 p hg
    simpa only [d1615, d47700, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3725 (p : Pattern) (guard : d1616 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1611 p = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3720 p hg
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1615 p = 1 := by simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3724 p hg
    simpa only [d1616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3726 (p : Pattern) (guard : d1617 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1616 p = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3725 p hg
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3727 (p : Pattern) (guard : d1618 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1617 p = 1 := by simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3726 p hg
    simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3728 (p : Pattern) (guard : d1619 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1618 p = 1 := by simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3727 p hg
    simpa only [d1619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3729 (p : Pattern) (guard : d1620 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1615 p = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3724 p hg
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3730 (p : Pattern) (guard : d1621 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1620 p = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3729 p hg
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3731 (p : Pattern) (guard : d1622 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1621 p = 1 := by simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3730 p hg
    simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3732 (p : Pattern) (guard : d1623 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1622 p = 1 := by simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3731 p hg
    simpa only [d1623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3733 (p : Pattern) (guard : d1624 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1619 p = 1 := by simpa only [d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3728 p hg
    simpa only [d1624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1623 p = 1 := by simpa only [d1624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3732 p hg
    simpa only [d1624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3734 (p : Pattern) (guard : d1625 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1624 p = 1 := by simpa only [d1625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3733 p hg
    simpa only [d1625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3735 (p : Pattern) (guard : d1626 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1625 p = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3734 p hg
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3736 (p : Pattern) (guard : d1627 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1626 p = 1 := by simpa only [d1627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3735 p hg
    simpa only [d1627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3737 (p : Pattern) (guard : d1628 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1627 p = 1 := by simpa only [d1628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3736 p hg
    simpa only [d1628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3738 (p : Pattern) (guard : d1629 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1629, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d1629, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1628 p = 1 := by simpa only [d1629, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3737 p hg
    simpa only [d1629, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3739 (p : Pattern) (guard : d1632 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1618 p = 1 := by simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3727 p hg
    simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3740 (p : Pattern) (guard : d1633 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1622 p = 1 := by simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3731 p hg
    simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3741 (p : Pattern) (guard : d1634 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1632 p = 1 := by simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3739 p hg
    simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1633 p = 1 := by simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3740 p hg
    simpa only [d1634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3742 (p : Pattern) (guard : d1635 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1634 p = 1 := by simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3741 p hg
    simpa only [d1635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3743 (p : Pattern) (guard : d1636 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1635 p = 1 := by simpa only [d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3742 p hg
    simpa only [d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3744 (p : Pattern) (guard : d1637 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1636 p = 1 := by simpa only [d1637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3743 p hg
    simpa only [d1637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3745 (p : Pattern) (guard : d1638 p = 1) : d47700 p ≤ (-1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3393 p hg
    simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1637 p = 1 := by simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3744 p hg
    simpa only [d1638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3746 (p : Pattern) (guard : d53764 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53764, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1131 p hg
    simpa only [d53764, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1638 p = 1 := by simpa only [d53764, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3745 p hg
    simpa only [d53764, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3747 (p : Pattern) (guard : d66008 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d1629 p = 1 := by simpa only [d66008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3738 p hg
    simpa only [d66008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53764 p = 1 := by simpa only [d66008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3746 p hg
    simpa only [d66008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3748 (p : Pattern) (guard : d66009 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d66008 p = 1 := by simpa only [d66009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3747 p hg
    simpa only [d66009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d66009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare3749 (p : Pattern) (guard : d66010 p = 1) : d47700 p ≤ (-1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d66009 p = 1 := by simpa only [d66010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3748 p hg
    simpa only [d66010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d66010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3392 p hg
    simpa only [d66010, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
