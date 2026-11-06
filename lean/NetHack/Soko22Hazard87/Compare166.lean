import NetHack.Soko22Hazard87.Compare165
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare41500 (p : Pattern) (guard : d348411 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348408 p = 1 := by simpa only [d348411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41489 p hg
    simpa only [d348411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348410 p = 1 := by simpa only [d348411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41499 p hg
    simpa only [d348411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41501 (p : Pattern) (guard : d348412 p = 1) : d51023 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348412, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41461 p hg
    simpa only [d348412, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348411 p = 1 := by simpa only [d348412, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41500 p hg
    simpa only [d348412, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41502 (p : Pattern) (guard : d348413 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348413, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41460 p hg
    simpa only [d348413, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348412 p = 1 := by simpa only [d348413, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41501 p hg
    simpa only [d348413, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41503 (p : Pattern) (guard : d348414 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348410 p = 1 := by simpa only [d348414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41499 p hg
    simpa only [d348414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41462 p hg
    simpa only [d348414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41504 (p : Pattern) (guard : d348415 p = 1) : d51023 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348415, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41461 p hg
    simpa only [d348415, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348414 p = 1 := by simpa only [d348415, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41503 p hg
    simpa only [d348415, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41505 (p : Pattern) (guard : d348416 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348416, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41460 p hg
    simpa only [d348416, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348415 p = 1 := by simpa only [d348416, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41504 p hg
    simpa only [d348416, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41506 (p : Pattern) (guard : d348417 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348413 p = 1 := by simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41502 p hg
    simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348416 p = 1 := by simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41505 p hg
    simpa only [d348417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41507 (p : Pattern) (guard : d348479 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348478 p = 1 := by simpa only [d348479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41498 p hg
    simpa only [d348479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348417 p = 1 := by simpa only [d348479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41506 p hg
    simpa only [d348479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41508 (p : Pattern) (guard : d0 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41509 (p : Pattern) (guard : d348480 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348479 p = 1 := by simpa only [d348480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41507 p hg
    simpa only [d348480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41508 p hg
    simpa only [d348480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41510 (p : Pattern) (guard : d0 p = 1) : d51035 p ≤ (1 : Int) + d47764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41511 (p : Pattern) (guard : d348481 p = 1) : d51036 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348480 p = 1 := by simpa only [d348481, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41509 p hg
    simpa only [d348481, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348481, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41510 p hg
    simpa only [d348481, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41512 (p : Pattern) (guard : d348482 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348482, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41459 p hg
    simpa only [d348482, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348481 p = 1 := by simpa only [d348482, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41511 p hg
    simpa only [d348482, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41513 (p : Pattern) (guard : d348418 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348416 p = 1 := by simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41505 p hg
    simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41508 p hg
    simpa only [d348418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41514 (p : Pattern) (guard : d348419 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348417 p = 1 := by simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41506 p hg
    simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348418 p = 1 := by simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41513 p hg
    simpa only [d348419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41515 (p : Pattern) (guard : d348420 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348419 p = 1 := by simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41514 p hg
    simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41508 p hg
    simpa only [d348420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41516 (p : Pattern) (guard : d348421 p = 1) : d51036 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348420 p = 1 := by simpa only [d348421, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41515 p hg
    simpa only [d348421, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348421, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41510 p hg
    simpa only [d348421, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41517 (p : Pattern) (guard : d348422 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348422, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41459 p hg
    simpa only [d348422, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348421 p = 1 := by simpa only [d348422, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41516 p hg
    simpa only [d348422, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41518 (p : Pattern) (guard : d348483 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348482 p = 1 := by simpa only [d348483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41512 p hg
    simpa only [d348483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348422 p = 1 := by simpa only [d348483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41517 p hg
    simpa only [d348483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41519 (p : Pattern) (guard : d348484 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348483 p = 1 := by simpa only [d348484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41518 p hg
    simpa only [d348484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41520 (p : Pattern) (guard : d348485 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348484 p = 1 := by simpa only [d348485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41519 p hg
    simpa only [d348485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41521 (p : Pattern) (guard : d348510 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348485 p = 1 := by simpa only [d348510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41520 p hg
    simpa only [d348510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41522 (p : Pattern) (guard : d348423 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348418 p = 1 := by simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41513 p hg
    simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41508 p hg
    simpa only [d348423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41523 (p : Pattern) (guard : d348424 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348423 p = 1 := by simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41522 p hg
    simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41508 p hg
    simpa only [d348424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41524 (p : Pattern) (guard : d348425 p = 1) : d51036 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348424 p = 1 := by simpa only [d348425, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41523 p hg
    simpa only [d348425, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348425, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41510 p hg
    simpa only [d348425, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41525 (p : Pattern) (guard : d348426 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348426, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41459 p hg
    simpa only [d348426, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348425 p = 1 := by simpa only [d348426, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41524 p hg
    simpa only [d348426, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41526 (p : Pattern) (guard : d348427 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348422 p = 1 := by simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41517 p hg
    simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348426 p = 1 := by simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41525 p hg
    simpa only [d348427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41527 (p : Pattern) (guard : d348428 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348427 p = 1 := by simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41526 p hg
    simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41528 (p : Pattern) (guard : d348429 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348428 p = 1 := by simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41527 p hg
    simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41529 (p : Pattern) (guard : d348443 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348429 p = 1 := by simpa only [d348443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41528 p hg
    simpa only [d348443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41530 (p : Pattern) (guard : d348511 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348510 p = 1 := by simpa only [d348511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41521 p hg
    simpa only [d348511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348443 p = 1 := by simpa only [d348511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41529 p hg
    simpa only [d348511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41531 (p : Pattern) (guard : d348512 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348511 p = 1 := by simpa only [d348512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41530 p hg
    simpa only [d348512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41532 (p : Pattern) (guard : d348489 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348422 p = 1 := by simpa only [d348489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41517 p hg
    simpa only [d348489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41533 (p : Pattern) (guard : d348490 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348489 p = 1 := by simpa only [d348490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41532 p hg
    simpa only [d348490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41534 (p : Pattern) (guard : d348491 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348490 p = 1 := by simpa only [d348491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41533 p hg
    simpa only [d348491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41535 (p : Pattern) (guard : d348513 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348491 p = 1 := by simpa only [d348513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41534 p hg
    simpa only [d348513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41536 (p : Pattern) (guard : d348514 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348513 p = 1 := by simpa only [d348514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41535 p hg
    simpa only [d348514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41537 (p : Pattern) (guard : d348515 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348514 p = 1 := by simpa only [d348515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41536 p hg
    simpa only [d348515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41538 (p : Pattern) (guard : d348516 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348512 p = 1 := by simpa only [d348516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41531 p hg
    simpa only [d348516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348515 p = 1 := by simpa only [d348516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41537 p hg
    simpa only [d348516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41539 (p : Pattern) (guard : d348537 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348516 p = 1 := by simpa only [d348537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41538 p hg
    simpa only [d348537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41540 (p : Pattern) (guard : d348538 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348537 p = 1 := by simpa only [d348538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41539 p hg
    simpa only [d348538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41541 (p : Pattern) (guard : d348539 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348539, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348539, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348538 p = 1 := by simpa only [d348539, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41540 p hg
    simpa only [d348539, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41542 (p : Pattern) (guard : d348540 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41457 p hg
    simpa only [d348540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348539 p = 1 := by simpa only [d348540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41541 p hg
    simpa only [d348540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41543 (p : Pattern) (guard : d348431 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348426 p = 1 := by simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41525 p hg
    simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41544 (p : Pattern) (guard : d348432 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348431 p = 1 := by simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41543 p hg
    simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41545 (p : Pattern) (guard : d348433 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348432 p = 1 := by simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41544 p hg
    simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41546 (p : Pattern) (guard : d348444 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348433 p = 1 := by simpa only [d348444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41545 p hg
    simpa only [d348444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41547 (p : Pattern) (guard : d348527 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348444 p = 1 := by simpa only [d348527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41546 p hg
    simpa only [d348527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41548 (p : Pattern) (guard : d348528 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348527 p = 1 := by simpa only [d348528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41547 p hg
    simpa only [d348528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41549 (p : Pattern) (guard : d348529 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348528 p = 1 := by simpa only [d348529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41548 p hg
    simpa only [d348529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41550 (p : Pattern) (guard : d348530 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348529 p = 1 := by simpa only [d348530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41549 p hg
    simpa only [d348530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41551 (p : Pattern) (guard : d348531 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348530 p = 1 := by simpa only [d348531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41550 p hg
    simpa only [d348531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41552 (p : Pattern) (guard : d348541 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348541, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348541, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348531 p = 1 := by simpa only [d348541, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41551 p hg
    simpa only [d348541, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41553 (p : Pattern) (guard : d348542 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41457 p hg
    simpa only [d348542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348541 p = 1 := by simpa only [d348542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41552 p hg
    simpa only [d348542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41554 (p : Pattern) (guard : d348543 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d348540 p = 1 := by simpa only [d348543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41542 p hg
    simpa only [d348543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348542 p = 1 := by simpa only [d348543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41553 p hg
    simpa only [d348543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41555 (p : Pattern) (guard : d348544 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d348543 p = 1 := by simpa only [d348544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41554 p hg
    simpa only [d348544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41457 p hg
    simpa only [d348544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41556 (p : Pattern) (guard : d348545 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d348544 p = 1 := by simpa only [d348545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41555 p hg
    simpa only [d348545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41457 p hg
    simpa only [d348545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41557 (p : Pattern) (guard : d348546 p = 1) : d51039 p ≤ (1 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d348536 p = 1 := by simpa only [d348546, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41456 p hg
    simpa only [d348546, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348545 p = 1 := by simpa only [d348546, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41556 p hg
    simpa only [d348546, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41558 (p : Pattern) (guard : d0 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41559 (p : Pattern) (guard : d0 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41560 (p : Pattern) (guard : d0 p = 1) : d51057 p ≤ (1 : Int) + d47786 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41561 (p : Pattern) (guard : d0 p = 1) : d51066 p ≤ (1 : Int) + d47796 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41562 (p : Pattern) (guard : d0 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41563 (p : Pattern) (guard : d0 p = 1) : d50874 p ≤ (1 : Int) + d47652 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41564 (p : Pattern) (guard : d0 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41565 (p : Pattern) (guard : d14 p = 1) : d2 p ≤ (1 : Int) + d2 p := by
  omega
theorem compare41566 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d47629 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41567 (p : Pattern) (guard : d15 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41565 p hg
    simpa only [d15, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41566 p hg
    simpa only [d15, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41568 (p : Pattern) (guard : d16 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41567 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41569 (p : Pattern) (guard : d17 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41568 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41570 (p : Pattern) (guard : d38813 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41569 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41571 (p : Pattern) (guard : d258091 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38813 p = 1 := by simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41570 p hg
    simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41572 (p : Pattern) (guard : d337158 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258091 p = 1 := by simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41571 p hg
    simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41573 (p : Pattern) (guard : d337173 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d337158 p = 1 := by simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41572 p hg
    simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41574 (p : Pattern) (guard : d257183 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d38813 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41570 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41575 (p : Pattern) (guard : d257184 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257183 p = 1 := by simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41574 p hg
    simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41576 (p : Pattern) (guard : d257185 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257184 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41575 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41577 (p : Pattern) (guard : d348400 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d337173 p = 1 := by simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41573 p hg
    simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41576 p hg
    simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41578 (p : Pattern) (guard : d0 p = 1) : d50850 p ≤ (1 : Int) + d47631 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41579 (p : Pattern) (guard : d348401 p = 1) : d50874 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d348400 p = 1 := by simpa only [d348401, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41577 p hg
    simpa only [d348401, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348401, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41578 p hg
    simpa only [d348401, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41580 (p : Pattern) (guard : d348402 p = 1) : d50874 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d348401 p = 1 := by simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41579 p hg
    simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41563 p hg
    simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41581 (p : Pattern) (guard : d348547 p = 1) : d50874 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41563 p hg
    simpa only [d348547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348402 p = 1 := by simpa only [d348547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41580 p hg
    simpa only [d348547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41582 (p : Pattern) (guard : d348403 p = 1) : d51067 p ≤ (1 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348402 p = 1 := by simpa only [d348403, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41245 p hg
    simpa only [d348403, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348403, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41482 p hg
    simpa only [d348403, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41583 (p : Pattern) (guard : d348548 p = 1) : d51068 p ≤ (1 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348547 p = 1 := by simpa only [d348548, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41581 p hg
    simpa only [d348548, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348403 p = 1 := by simpa only [d348548, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41582 p hg
    simpa only [d348548, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41584 (p : Pattern) (guard : d0 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41585 (p : Pattern) (guard : d14 p = 1) : d6 p ≤ (1 : Int) + d6 p := by
  omega
theorem compare41586 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d47633 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41587 (p : Pattern) (guard : d15 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 246 with
  | false =>
    have hg : d14 p = 1 := by simpa only [d15, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41585 p hg
    simpa only [d15, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41586 p hg
    simpa only [d15, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41588 (p : Pattern) (guard : d16 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 226 with
  | false =>
    have hg : d15 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41587 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41589 (p : Pattern) (guard : d17 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41588 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41590 (p : Pattern) (guard : d38813 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41589 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41591 (p : Pattern) (guard : d258091 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38813 p = 1 := by simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41590 p hg
    simpa only [d258091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41592 (p : Pattern) (guard : d337158 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258091 p = 1 := by simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41591 p hg
    simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d337158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41593 (p : Pattern) (guard : d337173 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d337158 p = 1 := by simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41592 p hg
    simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d337173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41594 (p : Pattern) (guard : d257183 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d38813 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41590 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41595 (p : Pattern) (guard : d257184 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257183 p = 1 := by simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41594 p hg
    simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d257184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41596 (p : Pattern) (guard : d257185 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257184 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41595 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41597 (p : Pattern) (guard : d348400 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d337173 p = 1 := by simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41593 p hg
    simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41596 p hg
    simpa only [d348400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41598 (p : Pattern) (guard : d0 p = 1) : d50853 p ≤ (1 : Int) + d47635 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41599 (p : Pattern) (guard : d348401 p = 1) : d50900 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d348400 p = 1 := by simpa only [d348401, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41597 p hg
    simpa only [d348401, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348401, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41598 p hg
    simpa only [d348401, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41600 (p : Pattern) (guard : d0 p = 1) : d50900 p ≤ (1 : Int) + d47677 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41601 (p : Pattern) (guard : d348402 p = 1) : d50900 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d348401 p = 1 := by simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41599 p hg
    simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41600 p hg
    simpa only [d348402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41602 (p : Pattern) (guard : d348403 p = 1) : d50908 p ≤ (1 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348402 p = 1 := by simpa only [d348403, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41601 p hg
    simpa only [d348403, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348403, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d348403, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41603 (p : Pattern) (guard : d348404 p = 1) : d50909 p ≤ (1 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348403 p = 1 := by simpa only [d348404, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41602 p hg
    simpa only [d348404, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348404, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d348404, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41604 (p : Pattern) (guard : d348549 p = 1) : d51069 p ≤ (1 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d348548 p = 1 := by simpa only [d348549, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41583 p hg
    simpa only [d348549, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348404 p = 1 := by simpa only [d348549, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41603 p hg
    simpa only [d348549, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41605 (p : Pattern) (guard : d0 p = 1) : d51072 p ≤ (1 : Int) + d47802 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41606 (p : Pattern) (guard : d348550 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d348549 p = 1 := by simpa only [d348550, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41604 p hg
    simpa only [d348550, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348550, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41605 p hg
    simpa only [d348550, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41607 (p : Pattern) (guard : d348551 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41562 p hg
    simpa only [d348551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348550 p = 1 := by simpa only [d348551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41606 p hg
    simpa only [d348551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41608 (p : Pattern) (guard : d348552 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41562 p hg
    simpa only [d348552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348551 p = 1 := by simpa only [d348552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41607 p hg
    simpa only [d348552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41609 (p : Pattern) (guard : d348553 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41562 p hg
    simpa only [d348553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348552 p = 1 := by simpa only [d348553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41608 p hg
    simpa only [d348553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41610 (p : Pattern) (guard : d348554 p = 1) : d51074 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348554, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41561 p hg
    simpa only [d348554, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348553 p = 1 := by simpa only [d348554, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41609 p hg
    simpa only [d348554, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41611 (p : Pattern) (guard : d348555 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348555, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41560 p hg
    simpa only [d348555, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348554 p = 1 := by simpa only [d348555, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41610 p hg
    simpa only [d348555, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41612 (p : Pattern) (guard : d348556 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d348550 p = 1 := by simpa only [d348556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41606 p hg
    simpa only [d348556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41562 p hg
    simpa only [d348556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41613 (p : Pattern) (guard : d348557 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d348551 p = 1 := by simpa only [d348557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41607 p hg
    simpa only [d348557, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348556 p = 1 := by simpa only [d348557, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41612 p hg
    simpa only [d348557, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41614 (p : Pattern) (guard : d348558 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348552 p = 1 := by simpa only [d348558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41608 p hg
    simpa only [d348558, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348557 p = 1 := by simpa only [d348558, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41613 p hg
    simpa only [d348558, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41615 (p : Pattern) (guard : d348559 p = 1) : d51074 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348559, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41561 p hg
    simpa only [d348559, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348558 p = 1 := by simpa only [d348559, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41614 p hg
    simpa only [d348559, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41616 (p : Pattern) (guard : d348560 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348560, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41560 p hg
    simpa only [d348560, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348559 p = 1 := by simpa only [d348560, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41615 p hg
    simpa only [d348560, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41617 (p : Pattern) (guard : d348561 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348555 p = 1 := by simpa only [d348561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41611 p hg
    simpa only [d348561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348560 p = 1 := by simpa only [d348561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41616 p hg
    simpa only [d348561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41618 (p : Pattern) (guard : d348562 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41562 p hg
    simpa only [d348562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348556 p = 1 := by simpa only [d348562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41612 p hg
    simpa only [d348562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41619 (p : Pattern) (guard : d348563 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348552 p = 1 := by simpa only [d348563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41608 p hg
    simpa only [d348563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348562 p = 1 := by simpa only [d348563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41618 p hg
    simpa only [d348563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41620 (p : Pattern) (guard : d348564 p = 1) : d51074 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348564, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41561 p hg
    simpa only [d348564, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348563 p = 1 := by simpa only [d348564, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41619 p hg
    simpa only [d348564, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41621 (p : Pattern) (guard : d348565 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348565, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41560 p hg
    simpa only [d348565, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348564 p = 1 := by simpa only [d348565, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41620 p hg
    simpa only [d348565, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41622 (p : Pattern) (guard : d348566 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348562 p = 1 := by simpa only [d348566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41618 p hg
    simpa only [d348566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41562 p hg
    simpa only [d348566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41623 (p : Pattern) (guard : d348567 p = 1) : d51074 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348567, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41561 p hg
    simpa only [d348567, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348566 p = 1 := by simpa only [d348567, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41622 p hg
    simpa only [d348567, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41624 (p : Pattern) (guard : d348568 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348568, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41560 p hg
    simpa only [d348568, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348567 p = 1 := by simpa only [d348568, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41623 p hg
    simpa only [d348568, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41625 (p : Pattern) (guard : d348569 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348565 p = 1 := by simpa only [d348569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41621 p hg
    simpa only [d348569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348568 p = 1 := by simpa only [d348569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41624 p hg
    simpa only [d348569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41626 (p : Pattern) (guard : d348570 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348561 p = 1 := by simpa only [d348570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41617 p hg
    simpa only [d348570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348569 p = 1 := by simpa only [d348570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41625 p hg
    simpa only [d348570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41627 (p : Pattern) (guard : d0 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41628 (p : Pattern) (guard : d348571 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348570 p = 1 := by simpa only [d348571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41626 p hg
    simpa only [d348571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41627 p hg
    simpa only [d348571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41629 (p : Pattern) (guard : d0 p = 1) : d51076 p ≤ (1 : Int) + d47806 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41630 (p : Pattern) (guard : d348572 p = 1) : d51077 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348571 p = 1 := by simpa only [d348572, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41628 p hg
    simpa only [d348572, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348572, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41629 p hg
    simpa only [d348572, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41631 (p : Pattern) (guard : d348573 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348573, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41223 p hg
    simpa only [d348573, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348572 p = 1 := by simpa only [d348573, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41630 p hg
    simpa only [d348573, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41632 (p : Pattern) (guard : d348574 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348568 p = 1 := by simpa only [d348574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41624 p hg
    simpa only [d348574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41627 p hg
    simpa only [d348574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41633 (p : Pattern) (guard : d348575 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348569 p = 1 := by simpa only [d348575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41625 p hg
    simpa only [d348575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348574 p = 1 := by simpa only [d348575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41632 p hg
    simpa only [d348575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41634 (p : Pattern) (guard : d348576 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348575 p = 1 := by simpa only [d348576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41633 p hg
    simpa only [d348576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41627 p hg
    simpa only [d348576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41635 (p : Pattern) (guard : d348577 p = 1) : d51077 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348576 p = 1 := by simpa only [d348577, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41634 p hg
    simpa only [d348577, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348577, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41629 p hg
    simpa only [d348577, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41636 (p : Pattern) (guard : d348578 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348578, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41223 p hg
    simpa only [d348578, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348577 p = 1 := by simpa only [d348578, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41635 p hg
    simpa only [d348578, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41637 (p : Pattern) (guard : d348579 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348573 p = 1 := by simpa only [d348579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41631 p hg
    simpa only [d348579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348578 p = 1 := by simpa only [d348579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41636 p hg
    simpa only [d348579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41638 (p : Pattern) (guard : d348580 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348579 p = 1 := by simpa only [d348580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41637 p hg
    simpa only [d348580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41639 (p : Pattern) (guard : d348581 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348580 p = 1 := by simpa only [d348581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41638 p hg
    simpa only [d348581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41640 (p : Pattern) (guard : d348582 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348581 p = 1 := by simpa only [d348582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41639 p hg
    simpa only [d348582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41641 (p : Pattern) (guard : d348583 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348574 p = 1 := by simpa only [d348583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41632 p hg
    simpa only [d348583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41627 p hg
    simpa only [d348583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41642 (p : Pattern) (guard : d348584 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348583 p = 1 := by simpa only [d348584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41641 p hg
    simpa only [d348584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41627 p hg
    simpa only [d348584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41643 (p : Pattern) (guard : d348585 p = 1) : d51077 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348584 p = 1 := by simpa only [d348585, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41642 p hg
    simpa only [d348585, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348585, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41629 p hg
    simpa only [d348585, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41644 (p : Pattern) (guard : d348586 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348586, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41223 p hg
    simpa only [d348586, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348585 p = 1 := by simpa only [d348586, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41643 p hg
    simpa only [d348586, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41645 (p : Pattern) (guard : d348587 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348578 p = 1 := by simpa only [d348587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41636 p hg
    simpa only [d348587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348586 p = 1 := by simpa only [d348587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41644 p hg
    simpa only [d348587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41646 (p : Pattern) (guard : d348588 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348587 p = 1 := by simpa only [d348588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41645 p hg
    simpa only [d348588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41647 (p : Pattern) (guard : d348589 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348588 p = 1 := by simpa only [d348589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41646 p hg
    simpa only [d348589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41648 (p : Pattern) (guard : d348590 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348589 p = 1 := by simpa only [d348590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41647 p hg
    simpa only [d348590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41649 (p : Pattern) (guard : d348591 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348582 p = 1 := by simpa only [d348591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41640 p hg
    simpa only [d348591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348590 p = 1 := by simpa only [d348591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41648 p hg
    simpa only [d348591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41650 (p : Pattern) (guard : d348592 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348591 p = 1 := by simpa only [d348592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41649 p hg
    simpa only [d348592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41651 (p : Pattern) (guard : d348593 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348578 p = 1 := by simpa only [d348593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41636 p hg
    simpa only [d348593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41652 (p : Pattern) (guard : d348594 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348593 p = 1 := by simpa only [d348594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41651 p hg
    simpa only [d348594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41653 (p : Pattern) (guard : d348595 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348594 p = 1 := by simpa only [d348595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41652 p hg
    simpa only [d348595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41654 (p : Pattern) (guard : d348596 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348595 p = 1 := by simpa only [d348596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41653 p hg
    simpa only [d348596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41655 (p : Pattern) (guard : d348597 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348596 p = 1 := by simpa only [d348597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41654 p hg
    simpa only [d348597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41656 (p : Pattern) (guard : d348598 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348597 p = 1 := by simpa only [d348598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41655 p hg
    simpa only [d348598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41657 (p : Pattern) (guard : d348599 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348592 p = 1 := by simpa only [d348599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41650 p hg
    simpa only [d348599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348598 p = 1 := by simpa only [d348599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41656 p hg
    simpa only [d348599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41658 (p : Pattern) (guard : d348600 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348599 p = 1 := by simpa only [d348600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41657 p hg
    simpa only [d348600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41659 (p : Pattern) (guard : d348601 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348600 p = 1 := by simpa only [d348601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41658 p hg
    simpa only [d348601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41660 (p : Pattern) (guard : d348602 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348602, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348602, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348601 p = 1 := by simpa only [d348602, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41659 p hg
    simpa only [d348602, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41661 (p : Pattern) (guard : d348603 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41558 p hg
    simpa only [d348603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348602 p = 1 := by simpa only [d348603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41660 p hg
    simpa only [d348603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41662 (p : Pattern) (guard : d348604 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348586 p = 1 := by simpa only [d348604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41644 p hg
    simpa only [d348604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41663 (p : Pattern) (guard : d348605 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348604 p = 1 := by simpa only [d348605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41662 p hg
    simpa only [d348605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41664 (p : Pattern) (guard : d348606 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348605 p = 1 := by simpa only [d348606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41663 p hg
    simpa only [d348606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41665 (p : Pattern) (guard : d348607 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348606 p = 1 := by simpa only [d348607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41664 p hg
    simpa only [d348607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41666 (p : Pattern) (guard : d348608 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348607 p = 1 := by simpa only [d348608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41665 p hg
    simpa only [d348608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41667 (p : Pattern) (guard : d348609 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348608 p = 1 := by simpa only [d348609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41666 p hg
    simpa only [d348609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41668 (p : Pattern) (guard : d348610 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348609 p = 1 := by simpa only [d348610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41667 p hg
    simpa only [d348610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41669 (p : Pattern) (guard : d348611 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348610 p = 1 := by simpa only [d348611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41668 p hg
    simpa only [d348611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41670 (p : Pattern) (guard : d348612 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348611 p = 1 := by simpa only [d348612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41669 p hg
    simpa only [d348612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41671 (p : Pattern) (guard : d348613 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348613, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348613, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348612 p = 1 := by simpa only [d348613, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41670 p hg
    simpa only [d348613, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41672 (p : Pattern) (guard : d348614 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41558 p hg
    simpa only [d348614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348613 p = 1 := by simpa only [d348614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41671 p hg
    simpa only [d348614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41673 (p : Pattern) (guard : d348615 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d348603 p = 1 := by simpa only [d348615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41661 p hg
    simpa only [d348615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348614 p = 1 := by simpa only [d348615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41672 p hg
    simpa only [d348615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41674 (p : Pattern) (guard : d348616 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d348615 p = 1 := by simpa only [d348616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41673 p hg
    simpa only [d348616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41558 p hg
    simpa only [d348616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41675 (p : Pattern) (guard : d348617 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d348616 p = 1 := by simpa only [d348617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41674 p hg
    simpa only [d348617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41558 p hg
    simpa only [d348617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41676 (p : Pattern) (guard : d0 p = 1) : d51136 p ≤ (1 : Int) + d47864 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare41677 (p : Pattern) (guard : d348618 p = 1) : d51137 p ≤ (1 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d348617 p = 1 := by simpa only [d348618, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41675 p hg
    simpa only [d348618, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348618, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41676 p hg
    simpa only [d348618, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41678 (p : Pattern) (guard : d348619 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d348546 p = 1 := by simpa only [d348619, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41557 p hg
    simpa only [d348619, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348618 p = 1 := by simpa only [d348619, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41677 p hg
    simpa only [d348619, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41679 (p : Pattern) (guard : d348620 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348619 p = 1 := by simpa only [d348620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41678 p hg
    simpa only [d348620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41680 (p : Pattern) (guard : d348621 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348620 p = 1 := by simpa only [d348621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41679 p hg
    simpa only [d348621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41681 (p : Pattern) (guard : d348622 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348621 p = 1 := by simpa only [d348622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41680 p hg
    simpa only [d348622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41682 (p : Pattern) (guard : d348623 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348622 p = 1 := by simpa only [d348623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41681 p hg
    simpa only [d348623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41683 (p : Pattern) (guard : d348624 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348623 p = 1 := by simpa only [d348624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41682 p hg
    simpa only [d348624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41684 (p : Pattern) (guard : d348625 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348624 p = 1 := by simpa only [d348625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41683 p hg
    simpa only [d348625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41685 (p : Pattern) (guard : d348626 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348625 p = 1 := by simpa only [d348626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41684 p hg
    simpa only [d348626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41686 (p : Pattern) (guard : d348627 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348626 p = 1 := by simpa only [d348627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41685 p hg
    simpa only [d348627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41687 (p : Pattern) (guard : d348628 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348627 p = 1 := by simpa only [d348628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41686 p hg
    simpa only [d348628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41688 (p : Pattern) (guard : d308 p = 1) : d4 p ≤ (1 : Int) + d4 p := by
  omega
theorem compare41689 (p : Pattern) (guard : d1519 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41688 p hg
    simpa only [d1519, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41230 p hg
    simpa only [d1519, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41690 (p : Pattern) (guard : d1531 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41689 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41691 (p : Pattern) (guard : d1547 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41690 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41692 (p : Pattern) (guard : d39244 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41691 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41693 (p : Pattern) (guard : d337457 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d39244 p = 1 := by simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41692 p hg
    simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41694 (p : Pattern) (guard : d337458 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d337457 p = 1 := by simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41693 p hg
    simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41695 (p : Pattern) (guard : d337473 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d337458 p = 1 := by simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41694 p hg
    simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41696 (p : Pattern) (guard : d258107 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d39244 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41692 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41697 (p : Pattern) (guard : d258108 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258107 p = 1 := by simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41696 p hg
    simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41698 (p : Pattern) (guard : d258109 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258108 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41697 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41699 (p : Pattern) (guard : d348629 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d337473 p = 1 := by simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41695 p hg
    simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41698 p hg
    simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41700 (p : Pattern) (guard : d348630 p = 1) : d50840 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d348629 p = 1 := by simpa only [d348630, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41699 p hg
    simpa only [d348630, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348630, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41242 p hg
    simpa only [d348630, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41701 (p : Pattern) (guard : d348631 p = 1) : d50840 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d348630 p = 1 := by simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41700 p hg
    simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41244 p hg
    simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41702 (p : Pattern) (guard : d348632 p = 1) : d50881 p ≤ (1 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348631 p = 1 := by simpa only [d348632, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41701 p hg
    simpa only [d348632, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348632, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41246 p hg
    simpa only [d348632, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41703 (p : Pattern) (guard : d348633 p = 1) : d50884 p ≤ (1 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348632 p = 1 := by simpa only [d348633, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41702 p hg
    simpa only [d348633, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348633, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41248 p hg
    simpa only [d348633, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41704 (p : Pattern) (guard : d348634 p = 1) : d50907 p ≤ (1 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348634, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41227 p hg
    simpa only [d348634, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348633 p = 1 := by simpa only [d348634, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41703 p hg
    simpa only [d348634, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41705 (p : Pattern) (guard : d348635 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d348634 p = 1 := by simpa only [d348635, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41704 p hg
    simpa only [d348635, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348635, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41251 p hg
    simpa only [d348635, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41706 (p : Pattern) (guard : d348636 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41226 p hg
    simpa only [d348636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348635 p = 1 := by simpa only [d348636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41705 p hg
    simpa only [d348636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41707 (p : Pattern) (guard : d348637 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41226 p hg
    simpa only [d348637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348636 p = 1 := by simpa only [d348637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41706 p hg
    simpa only [d348637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41708 (p : Pattern) (guard : d348638 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d348635 p = 1 := by simpa only [d348638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41705 p hg
    simpa only [d348638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41226 p hg
    simpa only [d348638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41709 (p : Pattern) (guard : d348639 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41226 p hg
    simpa only [d348639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348638 p = 1 := by simpa only [d348639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41708 p hg
    simpa only [d348639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41710 (p : Pattern) (guard : d348640 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348637 p = 1 := by simpa only [d348640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41707 p hg
    simpa only [d348640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348639 p = 1 := by simpa only [d348640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41709 p hg
    simpa only [d348640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41711 (p : Pattern) (guard : d348641 p = 1) : d50912 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348641, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41225 p hg
    simpa only [d348641, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348640 p = 1 := by simpa only [d348641, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41710 p hg
    simpa only [d348641, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41712 (p : Pattern) (guard : d348642 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348642, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41224 p hg
    simpa only [d348642, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348641 p = 1 := by simpa only [d348642, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41711 p hg
    simpa only [d348642, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41713 (p : Pattern) (guard : d348643 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348639 p = 1 := by simpa only [d348643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41709 p hg
    simpa only [d348643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41226 p hg
    simpa only [d348643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41714 (p : Pattern) (guard : d348644 p = 1) : d50912 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348644, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41225 p hg
    simpa only [d348644, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348643 p = 1 := by simpa only [d348644, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41713 p hg
    simpa only [d348644, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41715 (p : Pattern) (guard : d348645 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348645, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41224 p hg
    simpa only [d348645, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348644 p = 1 := by simpa only [d348645, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41714 p hg
    simpa only [d348645, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41716 (p : Pattern) (guard : d348646 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348642 p = 1 := by simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41712 p hg
    simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348645 p = 1 := by simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41715 p hg
    simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41717 (p : Pattern) (guard : d348647 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348645 p = 1 := by simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41715 p hg
    simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41264 p hg
    simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41718 (p : Pattern) (guard : d348648 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348646 p = 1 := by simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41716 p hg
    simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348647 p = 1 := by simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41717 p hg
    simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41719 (p : Pattern) (guard : d348649 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348648 p = 1 := by simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41718 p hg
    simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41264 p hg
    simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41720 (p : Pattern) (guard : d348650 p = 1) : d50953 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348649 p = 1 := by simpa only [d348650, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41719 p hg
    simpa only [d348650, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348650, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41268 p hg
    simpa only [d348650, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41721 (p : Pattern) (guard : d348651 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348651, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41223 p hg
    simpa only [d348651, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348650 p = 1 := by simpa only [d348651, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41720 p hg
    simpa only [d348651, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41722 (p : Pattern) (guard : d348652 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348647 p = 1 := by simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41717 p hg
    simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41264 p hg
    simpa only [d348652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41723 (p : Pattern) (guard : d348653 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348652 p = 1 := by simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41722 p hg
    simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41264 p hg
    simpa only [d348653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41724 (p : Pattern) (guard : d348654 p = 1) : d50953 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348653 p = 1 := by simpa only [d348654, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41723 p hg
    simpa only [d348654, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348654, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41268 p hg
    simpa only [d348654, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41725 (p : Pattern) (guard : d348655 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348655, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41223 p hg
    simpa only [d348655, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348654 p = 1 := by simpa only [d348655, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41724 p hg
    simpa only [d348655, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41726 (p : Pattern) (guard : d348656 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348651 p = 1 := by simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41721 p hg
    simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348655 p = 1 := by simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41725 p hg
    simpa only [d348656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41727 (p : Pattern) (guard : d348657 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348656 p = 1 := by simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41726 p hg
    simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41728 (p : Pattern) (guard : d348658 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348657 p = 1 := by simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41727 p hg
    simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41729 (p : Pattern) (guard : d348659 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348658 p = 1 := by simpa only [d348659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41728 p hg
    simpa only [d348659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41730 (p : Pattern) (guard : d348660 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348655 p = 1 := by simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41725 p hg
    simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41731 (p : Pattern) (guard : d348661 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348660 p = 1 := by simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41730 p hg
    simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41732 (p : Pattern) (guard : d348662 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348661 p = 1 := by simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41731 p hg
    simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41733 (p : Pattern) (guard : d348663 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348662 p = 1 := by simpa only [d348663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41732 p hg
    simpa only [d348663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41734 (p : Pattern) (guard : d348664 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348659 p = 1 := by simpa only [d348664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41729 p hg
    simpa only [d348664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348663 p = 1 := by simpa only [d348664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41733 p hg
    simpa only [d348664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41735 (p : Pattern) (guard : d348665 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348664 p = 1 := by simpa only [d348665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41734 p hg
    simpa only [d348665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41736 (p : Pattern) (guard : d348666 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348665 p = 1 := by simpa only [d348666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41735 p hg
    simpa only [d348666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41737 (p : Pattern) (guard : d348667 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348666 p = 1 := by simpa only [d348667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41736 p hg
    simpa only [d348667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41738 (p : Pattern) (guard : d348668 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348667 p = 1 := by simpa only [d348668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41737 p hg
    simpa only [d348668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41739 (p : Pattern) (guard : d348669 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348669, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348669, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348668 p = 1 := by simpa only [d348669, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41738 p hg
    simpa only [d348669, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41740 (p : Pattern) (guard : d348670 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41220 p hg
    simpa only [d348670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348669 p = 1 := by simpa only [d348670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41739 p hg
    simpa only [d348670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41741 (p : Pattern) (guard : d348671 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d348670 p = 1 := by simpa only [d348671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41740 p hg
    simpa only [d348671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41220 p hg
    simpa only [d348671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41742 (p : Pattern) (guard : d348642 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348642, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41292 p hg
    simpa only [d348642, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348641 p = 1 := by simpa only [d348642, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41711 p hg
    simpa only [d348642, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41743 (p : Pattern) (guard : d348645 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348645, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41292 p hg
    simpa only [d348645, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348644 p = 1 := by simpa only [d348645, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41714 p hg
    simpa only [d348645, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41744 (p : Pattern) (guard : d348646 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348642 p = 1 := by simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41742 p hg
    simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348645 p = 1 := by simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41743 p hg
    simpa only [d348646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41745 (p : Pattern) (guard : d348647 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348645 p = 1 := by simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41743 p hg
    simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41296 p hg
    simpa only [d348647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41746 (p : Pattern) (guard : d348648 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348646 p = 1 := by simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41744 p hg
    simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348647 p = 1 := by simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41745 p hg
    simpa only [d348648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41747 (p : Pattern) (guard : d348649 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348648 p = 1 := by simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41746 p hg
    simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41296 p hg
    simpa only [d348649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41748 (p : Pattern) (guard : d348650 p = 1) : d50932 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348649 p = 1 := by simpa only [d348650, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41747 p hg
    simpa only [d348650, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348650, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41268 p hg
    simpa only [d348650, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare41749 (p : Pattern) (guard : d348651 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348651, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41291 p hg
    simpa only [d348651, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348650 p = 1 := by simpa only [d348651, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41748 p hg
    simpa only [d348651, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
