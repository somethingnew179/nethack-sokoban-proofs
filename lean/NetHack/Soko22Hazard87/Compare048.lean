import NetHack.Soko22Hazard87.Compare047
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare12000 (p : Pattern) (guard : d160493 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160484 p = 1 := by simpa only [d160493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11991 p hg
    simpa only [d160493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12001 (p : Pattern) (guard : d160494 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160493 p = 1 := by simpa only [d160494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12000 p hg
    simpa only [d160494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12002 (p : Pattern) (guard : d160495 p = 1) : d47807 p ≤ (-1 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160494 p = 1 := by simpa only [d160495, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12001 p hg
    simpa only [d160495, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160495, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d160495, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12003 (p : Pattern) (guard : d160496 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160496, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160496, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160495 p = 1 := by simpa only [d160496, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12002 p hg
    simpa only [d160496, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12004 (p : Pattern) (guard : d160497 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160488 p = 1 := by simpa only [d160497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11995 p hg
    simpa only [d160497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160496 p = 1 := by simpa only [d160497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12003 p hg
    simpa only [d160497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12005 (p : Pattern) (guard : d160498 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160497 p = 1 := by simpa only [d160498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12004 p hg
    simpa only [d160498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12006 (p : Pattern) (guard : d160499 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160498 p = 1 := by simpa only [d160499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12005 p hg
    simpa only [d160499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12007 (p : Pattern) (guard : d160500 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160499 p = 1 := by simpa only [d160500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12006 p hg
    simpa only [d160500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12008 (p : Pattern) (guard : d160501 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160492 p = 1 := by simpa only [d160501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11999 p hg
    simpa only [d160501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160500 p = 1 := by simpa only [d160501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12007 p hg
    simpa only [d160501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12009 (p : Pattern) (guard : d160502 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160501 p = 1 := by simpa only [d160502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12008 p hg
    simpa only [d160502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12010 (p : Pattern) (guard : d160503 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160488 p = 1 := by simpa only [d160503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11995 p hg
    simpa only [d160503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12011 (p : Pattern) (guard : d160504 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160503 p = 1 := by simpa only [d160504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12010 p hg
    simpa only [d160504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12012 (p : Pattern) (guard : d160505 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160504 p = 1 := by simpa only [d160505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12011 p hg
    simpa only [d160505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12013 (p : Pattern) (guard : d160506 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160505 p = 1 := by simpa only [d160506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12012 p hg
    simpa only [d160506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12014 (p : Pattern) (guard : d160507 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160506 p = 1 := by simpa only [d160507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12013 p hg
    simpa only [d160507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12015 (p : Pattern) (guard : d160508 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160507 p = 1 := by simpa only [d160508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12014 p hg
    simpa only [d160508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12016 (p : Pattern) (guard : d160509 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160502 p = 1 := by simpa only [d160509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12009 p hg
    simpa only [d160509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160508 p = 1 := by simpa only [d160509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12015 p hg
    simpa only [d160509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12017 (p : Pattern) (guard : d160510 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160509 p = 1 := by simpa only [d160510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12016 p hg
    simpa only [d160510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12018 (p : Pattern) (guard : d160511 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160510 p = 1 := by simpa only [d160511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12017 p hg
    simpa only [d160511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12019 (p : Pattern) (guard : d160512 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160512, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160512, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160511 p = 1 := by simpa only [d160512, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12018 p hg
    simpa only [d160512, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12020 (p : Pattern) (guard : d160513 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160512 p = 1 := by simpa only [d160513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12019 p hg
    simpa only [d160513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12021 (p : Pattern) (guard : d160514 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160496 p = 1 := by simpa only [d160514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12003 p hg
    simpa only [d160514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12022 (p : Pattern) (guard : d160515 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160514 p = 1 := by simpa only [d160515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12021 p hg
    simpa only [d160515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12023 (p : Pattern) (guard : d160516 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160515 p = 1 := by simpa only [d160516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12022 p hg
    simpa only [d160516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12024 (p : Pattern) (guard : d160517 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160516 p = 1 := by simpa only [d160517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12023 p hg
    simpa only [d160517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12025 (p : Pattern) (guard : d160518 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160517 p = 1 := by simpa only [d160518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12024 p hg
    simpa only [d160518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12026 (p : Pattern) (guard : d160519 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160518 p = 1 := by simpa only [d160519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12025 p hg
    simpa only [d160519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12027 (p : Pattern) (guard : d160520 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160519 p = 1 := by simpa only [d160520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12026 p hg
    simpa only [d160520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12028 (p : Pattern) (guard : d160521 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160520 p = 1 := by simpa only [d160521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12027 p hg
    simpa only [d160521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12029 (p : Pattern) (guard : d160522 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160521 p = 1 := by simpa only [d160522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12028 p hg
    simpa only [d160522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12030 (p : Pattern) (guard : d160523 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160523, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160523, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160522 p = 1 := by simpa only [d160523, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12029 p hg
    simpa only [d160523, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12031 (p : Pattern) (guard : d160524 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160524, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160523 p = 1 := by simpa only [d160524, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12030 p hg
    simpa only [d160524, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12032 (p : Pattern) (guard : d160525 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160513 p = 1 := by simpa only [d160525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12020 p hg
    simpa only [d160525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160524 p = 1 := by simpa only [d160525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12031 p hg
    simpa only [d160525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12033 (p : Pattern) (guard : d160526 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160525 p = 1 := by simpa only [d160526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12032 p hg
    simpa only [d160526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12034 (p : Pattern) (guard : d160527 p = 1) : d47809 p ≤ (-1 : Int) + d159783 p := by
  cases selected : p 50 with
  | false =>
    have hg : d160526 p = 1 := by simpa only [d160527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12033 p hg
    simpa only [d160527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11068 p hg
    simpa only [d160527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12035 (p : Pattern) (guard : d160528 p = 1) : d47865 p ≤ (-1 : Int) + d159794 p := by
  cases selected : p 49 with
  | false =>
    have hg : d160527 p = 1 := by simpa only [d160528, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12034 p hg
    simpa only [d160528, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160528, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11105 p hg
    simpa only [d160528, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12036 (p : Pattern) (guard : d160529 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 48 with
  | false =>
    have hg : d160457 p = 1 := by simpa only [d160529, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11931 p hg
    simpa only [d160529, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160528 p = 1 := by simpa only [d160529, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12035 p hg
    simpa only [d160529, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12037 (p : Pattern) (guard : d160530 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160529 p = 1 := by simpa only [d160530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12036 p hg
    simpa only [d160530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12038 (p : Pattern) (guard : d160531 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160530 p = 1 := by simpa only [d160531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12037 p hg
    simpa only [d160531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12039 (p : Pattern) (guard : d160532 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160531 p = 1 := by simpa only [d160532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12038 p hg
    simpa only [d160532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12040 (p : Pattern) (guard : d160533 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160532 p = 1 := by simpa only [d160533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12039 p hg
    simpa only [d160533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12041 (p : Pattern) (guard : d160534 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160533 p = 1 := by simpa only [d160534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12040 p hg
    simpa only [d160534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12042 (p : Pattern) (guard : d160535 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160534 p = 1 := by simpa only [d160535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12041 p hg
    simpa only [d160535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12043 (p : Pattern) (guard : d160536 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160535 p = 1 := by simpa only [d160536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12042 p hg
    simpa only [d160536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12044 (p : Pattern) (guard : d160537 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160536 p = 1 := by simpa only [d160537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12043 p hg
    simpa only [d160537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12045 (p : Pattern) (guard : d160538 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d160314 p = 1 := by simpa only [d160538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11693 p hg
    simpa only [d160538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160537 p = 1 := by simpa only [d160538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12044 p hg
    simpa only [d160538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12046 (p : Pattern) (guard : d1572 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d1572, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6486 p hg
    simpa only [d1572, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12047 (p : Pattern) (guard : d1573 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12046 p hg
    simpa only [d1573, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d1573, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12048 (p : Pattern) (guard : d160539 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1573 p = 1 := by simpa only [d160539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12047 p hg
    simpa only [d160539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12049 (p : Pattern) (guard : d160540 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160539 p = 1 := by simpa only [d160540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12048 p hg
    simpa only [d160540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12050 (p : Pattern) (guard : d1584 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d1584, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6498 p hg
    simpa only [d1584, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12051 (p : Pattern) (guard : d1585 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12050 p hg
    simpa only [d1585, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d1585, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12052 (p : Pattern) (guard : d160541 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1585 p = 1 := by simpa only [d160541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12051 p hg
    simpa only [d160541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12053 (p : Pattern) (guard : d160542 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160541 p = 1 := by simpa only [d160542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12052 p hg
    simpa only [d160542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12054 (p : Pattern) (guard : d160543 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160540 p = 1 := by simpa only [d160543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12049 p hg
    simpa only [d160543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160542 p = 1 := by simpa only [d160543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12053 p hg
    simpa only [d160543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12055 (p : Pattern) (guard : d160544 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160544, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d160544, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160543 p = 1 := by simpa only [d160544, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12054 p hg
    simpa only [d160544, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12056 (p : Pattern) (guard : d160545 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160545, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d160545, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160544 p = 1 := by simpa only [d160545, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12055 p hg
    simpa only [d160545, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12057 (p : Pattern) (guard : d160546 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160542 p = 1 := by simpa only [d160546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12053 p hg
    simpa only [d160546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12058 (p : Pattern) (guard : d160547 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160547, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d160547, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160546 p = 1 := by simpa only [d160547, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12057 p hg
    simpa only [d160547, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12059 (p : Pattern) (guard : d160548 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160548, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d160548, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160547 p = 1 := by simpa only [d160548, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12058 p hg
    simpa only [d160548, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12060 (p : Pattern) (guard : d160549 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160545 p = 1 := by simpa only [d160549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12056 p hg
    simpa only [d160549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160548 p = 1 := by simpa only [d160549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12059 p hg
    simpa only [d160549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12061 (p : Pattern) (guard : d160550 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160548 p = 1 := by simpa only [d160550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12059 p hg
    simpa only [d160550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12062 (p : Pattern) (guard : d160551 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160549 p = 1 := by simpa only [d160551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12060 p hg
    simpa only [d160551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160550 p = 1 := by simpa only [d160551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12061 p hg
    simpa only [d160551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12063 (p : Pattern) (guard : d160552 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160551 p = 1 := by simpa only [d160552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12062 p hg
    simpa only [d160552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12064 (p : Pattern) (guard : d160553 p = 1) : d47699 p ≤ (-1 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160552 p = 1 := by simpa only [d160553, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12063 p hg
    simpa only [d160553, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160553, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d160553, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12065 (p : Pattern) (guard : d160554 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160554, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160554, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160553 p = 1 := by simpa only [d160554, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12064 p hg
    simpa only [d160554, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12066 (p : Pattern) (guard : d160555 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160550 p = 1 := by simpa only [d160555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12061 p hg
    simpa only [d160555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12067 (p : Pattern) (guard : d160556 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160555 p = 1 := by simpa only [d160556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12066 p hg
    simpa only [d160556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12068 (p : Pattern) (guard : d160557 p = 1) : d47699 p ≤ (-1 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160556 p = 1 := by simpa only [d160557, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12067 p hg
    simpa only [d160557, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160557, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d160557, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12069 (p : Pattern) (guard : d160558 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160558, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160558, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160557 p = 1 := by simpa only [d160558, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12068 p hg
    simpa only [d160558, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12070 (p : Pattern) (guard : d160559 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160554 p = 1 := by simpa only [d160559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12065 p hg
    simpa only [d160559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160558 p = 1 := by simpa only [d160559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12069 p hg
    simpa only [d160559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12071 (p : Pattern) (guard : d160560 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160559 p = 1 := by simpa only [d160560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12070 p hg
    simpa only [d160560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12072 (p : Pattern) (guard : d160561 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160560 p = 1 := by simpa only [d160561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12071 p hg
    simpa only [d160561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12073 (p : Pattern) (guard : d160562 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160561 p = 1 := by simpa only [d160562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12072 p hg
    simpa only [d160562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12074 (p : Pattern) (guard : d160563 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160558 p = 1 := by simpa only [d160563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12069 p hg
    simpa only [d160563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12075 (p : Pattern) (guard : d160564 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160563 p = 1 := by simpa only [d160564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12074 p hg
    simpa only [d160564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12076 (p : Pattern) (guard : d160565 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160564 p = 1 := by simpa only [d160565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12075 p hg
    simpa only [d160565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12077 (p : Pattern) (guard : d160566 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160565 p = 1 := by simpa only [d160566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12076 p hg
    simpa only [d160566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12078 (p : Pattern) (guard : d160567 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160562 p = 1 := by simpa only [d160567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12073 p hg
    simpa only [d160567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160566 p = 1 := by simpa only [d160567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12077 p hg
    simpa only [d160567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12079 (p : Pattern) (guard : d160568 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160567 p = 1 := by simpa only [d160568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12078 p hg
    simpa only [d160568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12080 (p : Pattern) (guard : d160569 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160568 p = 1 := by simpa only [d160569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12079 p hg
    simpa only [d160569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12081 (p : Pattern) (guard : d160570 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160569 p = 1 := by simpa only [d160570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12080 p hg
    simpa only [d160570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12082 (p : Pattern) (guard : d160571 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160570 p = 1 := by simpa only [d160571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12081 p hg
    simpa only [d160571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12083 (p : Pattern) (guard : d160572 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160571 p = 1 := by simpa only [d160572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12082 p hg
    simpa only [d160572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12084 (p : Pattern) (guard : d160573 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160572 p = 1 := by simpa only [d160573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12083 p hg
    simpa only [d160573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12085 (p : Pattern) (guard : d160574 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160573 p = 1 := by simpa only [d160574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12084 p hg
    simpa only [d160574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12086 (p : Pattern) (guard : d160575 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160561 p = 1 := by simpa only [d160575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12072 p hg
    simpa only [d160575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12087 (p : Pattern) (guard : d160576 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160565 p = 1 := by simpa only [d160576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12076 p hg
    simpa only [d160576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12088 (p : Pattern) (guard : d160577 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160575 p = 1 := by simpa only [d160577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12086 p hg
    simpa only [d160577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160576 p = 1 := by simpa only [d160577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12087 p hg
    simpa only [d160577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12089 (p : Pattern) (guard : d160578 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160577 p = 1 := by simpa only [d160578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12088 p hg
    simpa only [d160578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12090 (p : Pattern) (guard : d160579 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160578 p = 1 := by simpa only [d160579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12089 p hg
    simpa only [d160579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12091 (p : Pattern) (guard : d160580 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160579 p = 1 := by simpa only [d160580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12090 p hg
    simpa only [d160580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12092 (p : Pattern) (guard : d160581 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160580 p = 1 := by simpa only [d160581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12091 p hg
    simpa only [d160581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12093 (p : Pattern) (guard : d160582 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160571 p = 1 := by simpa only [d160582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12082 p hg
    simpa only [d160582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160581 p = 1 := by simpa only [d160582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12092 p hg
    simpa only [d160582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12094 (p : Pattern) (guard : d160583 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160572 p = 1 := by simpa only [d160583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12083 p hg
    simpa only [d160583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160582 p = 1 := by simpa only [d160583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12093 p hg
    simpa only [d160583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12095 (p : Pattern) (guard : d160584 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160583 p = 1 := by simpa only [d160584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12094 p hg
    simpa only [d160584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12096 (p : Pattern) (guard : d160585 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160574 p = 1 := by simpa only [d160585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12085 p hg
    simpa only [d160585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160584 p = 1 := by simpa only [d160585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12095 p hg
    simpa only [d160585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12097 (p : Pattern) (guard : d160586 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160560 p = 1 := by simpa only [d160586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12071 p hg
    simpa only [d160586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12098 (p : Pattern) (guard : d160587 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160586 p = 1 := by simpa only [d160587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12097 p hg
    simpa only [d160587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12099 (p : Pattern) (guard : d160588 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160564 p = 1 := by simpa only [d160588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12075 p hg
    simpa only [d160588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12100 (p : Pattern) (guard : d160589 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160588 p = 1 := by simpa only [d160589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12099 p hg
    simpa only [d160589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12101 (p : Pattern) (guard : d160590 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160587 p = 1 := by simpa only [d160590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12098 p hg
    simpa only [d160590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160589 p = 1 := by simpa only [d160590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12100 p hg
    simpa only [d160590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12102 (p : Pattern) (guard : d160591 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160590 p = 1 := by simpa only [d160591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12101 p hg
    simpa only [d160591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12103 (p : Pattern) (guard : d160592 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160591 p = 1 := by simpa only [d160592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12102 p hg
    simpa only [d160592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12104 (p : Pattern) (guard : d160593 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160592 p = 1 := by simpa only [d160593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12103 p hg
    simpa only [d160593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12105 (p : Pattern) (guard : d160594 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160559 p = 1 := by simpa only [d160594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12070 p hg
    simpa only [d160594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12106 (p : Pattern) (guard : d160595 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160594 p = 1 := by simpa only [d160595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12105 p hg
    simpa only [d160595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12107 (p : Pattern) (guard : d160596 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160595 p = 1 := by simpa only [d160596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12106 p hg
    simpa only [d160596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12108 (p : Pattern) (guard : d160597 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160563 p = 1 := by simpa only [d160597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12074 p hg
    simpa only [d160597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12109 (p : Pattern) (guard : d160598 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160597 p = 1 := by simpa only [d160598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12108 p hg
    simpa only [d160598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12110 (p : Pattern) (guard : d160599 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160598 p = 1 := by simpa only [d160599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12109 p hg
    simpa only [d160599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12111 (p : Pattern) (guard : d160600 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160596 p = 1 := by simpa only [d160600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12107 p hg
    simpa only [d160600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160599 p = 1 := by simpa only [d160600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12110 p hg
    simpa only [d160600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12112 (p : Pattern) (guard : d160601 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160600 p = 1 := by simpa only [d160601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12111 p hg
    simpa only [d160601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12113 (p : Pattern) (guard : d160602 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160601 p = 1 := by simpa only [d160602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12112 p hg
    simpa only [d160602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12114 (p : Pattern) (guard : d1557 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1557, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d1557, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1557, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6471 p hg
    simpa only [d1557, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12115 (p : Pattern) (guard : d1558 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12114 p hg
    simpa only [d1558, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d1558, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12116 (p : Pattern) (guard : d160603 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1558 p = 1 := by simpa only [d160603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12115 p hg
    simpa only [d160603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12117 (p : Pattern) (guard : d160604 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160603 p = 1 := by simpa only [d160604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12116 p hg
    simpa only [d160604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12118 (p : Pattern) (guard : d160605 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160604 p = 1 := by simpa only [d160605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12117 p hg
    simpa only [d160605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160540 p = 1 := by simpa only [d160605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12049 p hg
    simpa only [d160605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12119 (p : Pattern) (guard : d160606 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160606, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d160606, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160605 p = 1 := by simpa only [d160606, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12118 p hg
    simpa only [d160606, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12120 (p : Pattern) (guard : d160607 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160607, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d160607, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160606 p = 1 := by simpa only [d160607, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12119 p hg
    simpa only [d160607, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12121 (p : Pattern) (guard : d10057 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5122 p = 1 := by simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6597 p hg
    simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12122 (p : Pattern) (guard : d10058 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10057 p = 1 := by simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12121 p hg
    simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12123 (p : Pattern) (guard : d10080 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6460 p hg
    simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10058 p = 1 := by simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12122 p hg
    simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12124 (p : Pattern) (guard : d10081 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6465 p hg
    simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12125 (p : Pattern) (guard : d10082 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10080 p = 1 := by simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12123 p hg
    simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10081 p = 1 := by simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12124 p hg
    simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12126 (p : Pattern) (guard : d10083 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10082 p = 1 := by simpa only [d10083, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12125 p hg
    simpa only [d10083, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10083, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d10083, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12127 (p : Pattern) (guard : d13350 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10083 p = 1 := by simpa only [d13350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12126 p hg
    simpa only [d13350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4418 p hg
    simpa only [d13350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12128 (p : Pattern) (guard : d13351 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d13350 p = 1 := by simpa only [d13351, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12127 p hg
    simpa only [d13351, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13351, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d13351, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12129 (p : Pattern) (guard : d13352 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d13351 p = 1 := by simpa only [d13352, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12128 p hg
    simpa only [d13352, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13352, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d13352, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12130 (p : Pattern) (guard : d13353 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13353, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d13353, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13352 p = 1 := by simpa only [d13353, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12129 p hg
    simpa only [d13353, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12131 (p : Pattern) (guard : d13354 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13353 p = 1 := by simpa only [d13354, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12130 p hg
    simpa only [d13354, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13354, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d13354, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12132 (p : Pattern) (guard : d160608 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13354 p = 1 := by simpa only [d160608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12131 p hg
    simpa only [d160608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12133 (p : Pattern) (guard : d160609 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160608 p = 1 := by simpa only [d160609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12132 p hg
    simpa only [d160609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12134 (p : Pattern) (guard : d160610 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160540 p = 1 := by simpa only [d160610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12049 p hg
    simpa only [d160610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160609 p = 1 := by simpa only [d160610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12133 p hg
    simpa only [d160610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12135 (p : Pattern) (guard : d160611 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160611, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d160611, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160610 p = 1 := by simpa only [d160611, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12134 p hg
    simpa only [d160611, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12136 (p : Pattern) (guard : d160612 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160612, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d160612, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160611 p = 1 := by simpa only [d160612, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12135 p hg
    simpa only [d160612, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12137 (p : Pattern) (guard : d160613 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160607 p = 1 := by simpa only [d160613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12120 p hg
    simpa only [d160613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160612 p = 1 := by simpa only [d160613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12136 p hg
    simpa only [d160613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12138 (p : Pattern) (guard : d160614 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160613 p = 1 := by simpa only [d160614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12137 p hg
    simpa only [d160614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160549 p = 1 := by simpa only [d160614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12060 p hg
    simpa only [d160614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12139 (p : Pattern) (guard : d160615 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160614 p = 1 := by simpa only [d160615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12138 p hg
    simpa only [d160615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12140 (p : Pattern) (guard : d160616 p = 1) : d47699 p ≤ (-1 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160615 p = 1 := by simpa only [d160616, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12139 p hg
    simpa only [d160616, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160616, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d160616, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12141 (p : Pattern) (guard : d160617 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160617, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160617, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160616 p = 1 := by simpa only [d160617, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12140 p hg
    simpa only [d160617, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12142 (p : Pattern) (guard : d160618 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160617 p = 1 := by simpa only [d160618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12141 p hg
    simpa only [d160618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160554 p = 1 := by simpa only [d160618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12065 p hg
    simpa only [d160618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12143 (p : Pattern) (guard : d160619 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160618 p = 1 := by simpa only [d160619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12142 p hg
    simpa only [d160619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12144 (p : Pattern) (guard : d160620 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160619 p = 1 := by simpa only [d160620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12143 p hg
    simpa only [d160620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12145 (p : Pattern) (guard : d160621 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160620 p = 1 := by simpa only [d160621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12144 p hg
    simpa only [d160621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12146 (p : Pattern) (guard : d160622 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160621 p = 1 := by simpa only [d160622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12145 p hg
    simpa only [d160622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160562 p = 1 := by simpa only [d160622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12073 p hg
    simpa only [d160622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12147 (p : Pattern) (guard : d160623 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160622 p = 1 := by simpa only [d160623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12146 p hg
    simpa only [d160623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12148 (p : Pattern) (guard : d160624 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160554 p = 1 := by simpa only [d160624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12065 p hg
    simpa only [d160624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12149 (p : Pattern) (guard : d160625 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160624 p = 1 := by simpa only [d160625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12148 p hg
    simpa only [d160625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12150 (p : Pattern) (guard : d160626 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160625 p = 1 := by simpa only [d160626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12149 p hg
    simpa only [d160626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12151 (p : Pattern) (guard : d160627 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160626 p = 1 := by simpa only [d160627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12150 p hg
    simpa only [d160627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12152 (p : Pattern) (guard : d160628 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160627 p = 1 := by simpa only [d160628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12151 p hg
    simpa only [d160628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12153 (p : Pattern) (guard : d160629 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160628 p = 1 := by simpa only [d160629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12152 p hg
    simpa only [d160629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12154 (p : Pattern) (guard : d160630 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160623 p = 1 := by simpa only [d160630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12147 p hg
    simpa only [d160630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160629 p = 1 := by simpa only [d160630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12153 p hg
    simpa only [d160630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12155 (p : Pattern) (guard : d160631 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d160602 p = 1 := by simpa only [d160631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12113 p hg
    simpa only [d160631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160630 p = 1 := by simpa only [d160631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12154 p hg
    simpa only [d160631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12156 (p : Pattern) (guard : d160632 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d160593 p = 1 := by simpa only [d160632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12104 p hg
    simpa only [d160632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160631 p = 1 := by simpa only [d160632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12155 p hg
    simpa only [d160632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12157 (p : Pattern) (guard : d160633 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160632 p = 1 := by simpa only [d160633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12156 p hg
    simpa only [d160633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12158 (p : Pattern) (guard : d160634 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160586 p = 1 := by simpa only [d160634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12097 p hg
    simpa only [d160634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12159 (p : Pattern) (guard : d160635 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160588 p = 1 := by simpa only [d160635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12099 p hg
    simpa only [d160635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12160 (p : Pattern) (guard : d160636 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160634 p = 1 := by simpa only [d160636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12158 p hg
    simpa only [d160636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160635 p = 1 := by simpa only [d160636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12159 p hg
    simpa only [d160636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12161 (p : Pattern) (guard : d160637 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160636 p = 1 := by simpa only [d160637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12160 p hg
    simpa only [d160637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12162 (p : Pattern) (guard : d160638 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160637 p = 1 := by simpa only [d160638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12161 p hg
    simpa only [d160638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12163 (p : Pattern) (guard : d160639 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160638 p = 1 := by simpa only [d160639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12162 p hg
    simpa only [d160639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12164 (p : Pattern) (guard : d160640 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160595 p = 1 := by simpa only [d160640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12106 p hg
    simpa only [d160640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12165 (p : Pattern) (guard : d160641 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160598 p = 1 := by simpa only [d160641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12109 p hg
    simpa only [d160641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12166 (p : Pattern) (guard : d160642 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160640 p = 1 := by simpa only [d160642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12164 p hg
    simpa only [d160642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160641 p = 1 := by simpa only [d160642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12165 p hg
    simpa only [d160642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12167 (p : Pattern) (guard : d160643 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160642 p = 1 := by simpa only [d160643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12166 p hg
    simpa only [d160643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12168 (p : Pattern) (guard : d160644 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160643 p = 1 := by simpa only [d160644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12167 p hg
    simpa only [d160644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12169 (p : Pattern) (guard : d160645 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160620 p = 1 := by simpa only [d160645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12144 p hg
    simpa only [d160645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12170 (p : Pattern) (guard : d160646 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160645 p = 1 := by simpa only [d160646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12169 p hg
    simpa only [d160646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160575 p = 1 := by simpa only [d160646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12086 p hg
    simpa only [d160646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12171 (p : Pattern) (guard : d160647 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160646 p = 1 := by simpa only [d160647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12170 p hg
    simpa only [d160647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12172 (p : Pattern) (guard : d160648 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160626 p = 1 := by simpa only [d160648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12150 p hg
    simpa only [d160648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12173 (p : Pattern) (guard : d160649 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160648 p = 1 := by simpa only [d160649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12172 p hg
    simpa only [d160649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12174 (p : Pattern) (guard : d160650 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160649 p = 1 := by simpa only [d160650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12173 p hg
    simpa only [d160650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12175 (p : Pattern) (guard : d160651 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160647 p = 1 := by simpa only [d160651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12171 p hg
    simpa only [d160651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160650 p = 1 := by simpa only [d160651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12174 p hg
    simpa only [d160651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12176 (p : Pattern) (guard : d160652 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d160644 p = 1 := by simpa only [d160652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12168 p hg
    simpa only [d160652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160651 p = 1 := by simpa only [d160652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12175 p hg
    simpa only [d160652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12177 (p : Pattern) (guard : d160653 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d160639 p = 1 := by simpa only [d160653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12163 p hg
    simpa only [d160653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160652 p = 1 := by simpa only [d160653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12176 p hg
    simpa only [d160653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12178 (p : Pattern) (guard : d160654 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160632 p = 1 := by simpa only [d160654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12156 p hg
    simpa only [d160654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160653 p = 1 := by simpa only [d160654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12177 p hg
    simpa only [d160654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12179 (p : Pattern) (guard : d160655 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160633 p = 1 := by simpa only [d160655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12157 p hg
    simpa only [d160655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160654 p = 1 := by simpa only [d160655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12178 p hg
    simpa only [d160655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12180 (p : Pattern) (guard : d160656 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160566 p = 1 := by simpa only [d160656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12077 p hg
    simpa only [d160656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12181 (p : Pattern) (guard : d160657 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160656 p = 1 := by simpa only [d160657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12180 p hg
    simpa only [d160657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12182 (p : Pattern) (guard : d160658 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160657 p = 1 := by simpa only [d160658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12181 p hg
    simpa only [d160658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12183 (p : Pattern) (guard : d160659 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160658 p = 1 := by simpa only [d160659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12182 p hg
    simpa only [d160659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12184 (p : Pattern) (guard : d160660 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160659 p = 1 := by simpa only [d160660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12183 p hg
    simpa only [d160660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12185 (p : Pattern) (guard : d160661 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160571 p = 1 := by simpa only [d160661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12082 p hg
    simpa only [d160661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160660 p = 1 := by simpa only [d160661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12184 p hg
    simpa only [d160661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12186 (p : Pattern) (guard : d160662 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160576 p = 1 := by simpa only [d160662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12087 p hg
    simpa only [d160662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12187 (p : Pattern) (guard : d160663 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160662 p = 1 := by simpa only [d160663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12186 p hg
    simpa only [d160663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12188 (p : Pattern) (guard : d160664 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160663 p = 1 := by simpa only [d160664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12187 p hg
    simpa only [d160664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12189 (p : Pattern) (guard : d160665 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160664 p = 1 := by simpa only [d160665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12188 p hg
    simpa only [d160665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12190 (p : Pattern) (guard : d160666 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160665 p = 1 := by simpa only [d160666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12189 p hg
    simpa only [d160666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12191 (p : Pattern) (guard : d160667 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160660 p = 1 := by simpa only [d160667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12184 p hg
    simpa only [d160667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160666 p = 1 := by simpa only [d160667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12190 p hg
    simpa only [d160667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12192 (p : Pattern) (guard : d160668 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160661 p = 1 := by simpa only [d160668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12185 p hg
    simpa only [d160668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160667 p = 1 := by simpa only [d160668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12191 p hg
    simpa only [d160668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12193 (p : Pattern) (guard : d160669 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160655 p = 1 := by simpa only [d160669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12179 p hg
    simpa only [d160669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160668 p = 1 := by simpa only [d160669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12192 p hg
    simpa only [d160669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12194 (p : Pattern) (guard : d160670 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160669 p = 1 := by simpa only [d160670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12193 p hg
    simpa only [d160670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12195 (p : Pattern) (guard : d160671 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 50 with
  | false =>
    have hg : d160585 p = 1 := by simpa only [d160671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12096 p hg
    simpa only [d160671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160670 p = 1 := by simpa only [d160671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12194 p hg
    simpa only [d160671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12196 (p : Pattern) (guard : d1557 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1557, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d1557, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1556 p = 1 := by simpa only [d1557, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6738 p hg
    simpa only [d1557, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12197 (p : Pattern) (guard : d1558 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1557 p = 1 := by simpa only [d1558, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12196 p hg
    simpa only [d1558, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1558, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d1558, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12198 (p : Pattern) (guard : d160603 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1558 p = 1 := by simpa only [d160603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12197 p hg
    simpa only [d160603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12199 (p : Pattern) (guard : d160604 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160603 p = 1 := by simpa only [d160604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12198 p hg
    simpa only [d160604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12200 (p : Pattern) (guard : d1572 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1572, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d1572, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1571 p = 1 := by simpa only [d1572, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6754 p hg
    simpa only [d1572, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12201 (p : Pattern) (guard : d1573 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1572 p = 1 := by simpa only [d1573, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12200 p hg
    simpa only [d1573, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1573, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d1573, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12202 (p : Pattern) (guard : d160539 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1573 p = 1 := by simpa only [d160539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12201 p hg
    simpa only [d160539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12203 (p : Pattern) (guard : d160540 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160539 p = 1 := by simpa only [d160540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12202 p hg
    simpa only [d160540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12204 (p : Pattern) (guard : d160605 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160604 p = 1 := by simpa only [d160605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12199 p hg
    simpa only [d160605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160540 p = 1 := by simpa only [d160605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12203 p hg
    simpa only [d160605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12205 (p : Pattern) (guard : d160606 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160606, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d160606, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160605 p = 1 := by simpa only [d160606, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12204 p hg
    simpa only [d160606, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12206 (p : Pattern) (guard : d160607 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160607, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d160607, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160606 p = 1 := by simpa only [d160607, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12205 p hg
    simpa only [d160607, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12207 (p : Pattern) (guard : d10057 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5122 p = 1 := by simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6802 p hg
    simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d10057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12208 (p : Pattern) (guard : d10058 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d10057 p = 1 := by simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12207 p hg
    simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d10058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12209 (p : Pattern) (guard : d10080 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1545 p = 1 := by simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6727 p hg
    simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10058 p = 1 := by simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12208 p hg
    simpa only [d10080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12210 (p : Pattern) (guard : d10081 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1550 p = 1 := by simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6732 p hg
    simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d10081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12211 (p : Pattern) (guard : d10082 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d10080 p = 1 := by simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12209 p hg
    simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10081 p = 1 := by simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12210 p hg
    simpa only [d10082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12212 (p : Pattern) (guard : d10083 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d10082 p = 1 := by simpa only [d10083, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12211 p hg
    simpa only [d10083, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10083, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d10083, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12213 (p : Pattern) (guard : d13350 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d10083 p = 1 := by simpa only [d13350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12212 p hg
    simpa only [d13350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4479 p hg
    simpa only [d13350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12214 (p : Pattern) (guard : d13351 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d13350 p = 1 := by simpa only [d13351, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12213 p hg
    simpa only [d13351, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13351, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d13351, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12215 (p : Pattern) (guard : d13352 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d13351 p = 1 := by simpa only [d13352, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12214 p hg
    simpa only [d13352, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13352, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d13352, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12216 (p : Pattern) (guard : d13353 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13353, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d13353, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13352 p = 1 := by simpa only [d13353, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12215 p hg
    simpa only [d13353, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12217 (p : Pattern) (guard : d13354 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13353 p = 1 := by simpa only [d13354, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12216 p hg
    simpa only [d13354, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13354, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d13354, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12218 (p : Pattern) (guard : d160608 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13354 p = 1 := by simpa only [d160608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12217 p hg
    simpa only [d160608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12219 (p : Pattern) (guard : d160609 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160608 p = 1 := by simpa only [d160609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12218 p hg
    simpa only [d160609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12220 (p : Pattern) (guard : d160610 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160540 p = 1 := by simpa only [d160610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12203 p hg
    simpa only [d160610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160609 p = 1 := by simpa only [d160610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12219 p hg
    simpa only [d160610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12221 (p : Pattern) (guard : d160611 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160611, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d160611, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160610 p = 1 := by simpa only [d160611, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12220 p hg
    simpa only [d160611, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12222 (p : Pattern) (guard : d160612 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160612, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d160612, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160611 p = 1 := by simpa only [d160612, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12221 p hg
    simpa only [d160612, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12223 (p : Pattern) (guard : d160613 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160607 p = 1 := by simpa only [d160613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12206 p hg
    simpa only [d160613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160612 p = 1 := by simpa only [d160613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12222 p hg
    simpa only [d160613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12224 (p : Pattern) (guard : d1584 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1584, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d1584, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1583 p = 1 := by simpa only [d1584, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6767 p hg
    simpa only [d1584, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12225 (p : Pattern) (guard : d1585 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1584 p = 1 := by simpa only [d1585, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12224 p hg
    simpa only [d1585, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1585, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d1585, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12226 (p : Pattern) (guard : d160541 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1585 p = 1 := by simpa only [d160541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12225 p hg
    simpa only [d160541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12227 (p : Pattern) (guard : d160542 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160541 p = 1 := by simpa only [d160542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12226 p hg
    simpa only [d160542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12228 (p : Pattern) (guard : d160543 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160540 p = 1 := by simpa only [d160543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12203 p hg
    simpa only [d160543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160542 p = 1 := by simpa only [d160543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12227 p hg
    simpa only [d160543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12229 (p : Pattern) (guard : d160544 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160544, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d160544, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160543 p = 1 := by simpa only [d160544, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12228 p hg
    simpa only [d160544, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12230 (p : Pattern) (guard : d160545 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160545, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d160545, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160544 p = 1 := by simpa only [d160545, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12229 p hg
    simpa only [d160545, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12231 (p : Pattern) (guard : d160546 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160542 p = 1 := by simpa only [d160546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12227 p hg
    simpa only [d160546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12232 (p : Pattern) (guard : d160547 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160547, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d160547, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160546 p = 1 := by simpa only [d160547, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12231 p hg
    simpa only [d160547, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12233 (p : Pattern) (guard : d160548 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160548, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d160548, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160547 p = 1 := by simpa only [d160548, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12232 p hg
    simpa only [d160548, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12234 (p : Pattern) (guard : d160549 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160545 p = 1 := by simpa only [d160549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12230 p hg
    simpa only [d160549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160548 p = 1 := by simpa only [d160549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12233 p hg
    simpa only [d160549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12235 (p : Pattern) (guard : d160614 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160613 p = 1 := by simpa only [d160614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12223 p hg
    simpa only [d160614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160549 p = 1 := by simpa only [d160614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12234 p hg
    simpa only [d160614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12236 (p : Pattern) (guard : d160615 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160614 p = 1 := by simpa only [d160615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12235 p hg
    simpa only [d160615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12237 (p : Pattern) (guard : d160616 p = 1) : d47765 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160615 p = 1 := by simpa only [d160616, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12236 p hg
    simpa only [d160616, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160616, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d160616, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12238 (p : Pattern) (guard : d160617 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160617, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d160617, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160616 p = 1 := by simpa only [d160617, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12237 p hg
    simpa only [d160617, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12239 (p : Pattern) (guard : d160550 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160548 p = 1 := by simpa only [d160550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12233 p hg
    simpa only [d160550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12240 (p : Pattern) (guard : d160551 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160549 p = 1 := by simpa only [d160551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12234 p hg
    simpa only [d160551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160550 p = 1 := by simpa only [d160551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12239 p hg
    simpa only [d160551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12241 (p : Pattern) (guard : d160552 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160551 p = 1 := by simpa only [d160552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12240 p hg
    simpa only [d160552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12242 (p : Pattern) (guard : d160553 p = 1) : d47765 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160552 p = 1 := by simpa only [d160553, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12241 p hg
    simpa only [d160553, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160553, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d160553, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12243 (p : Pattern) (guard : d160554 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160554, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d160554, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160553 p = 1 := by simpa only [d160554, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12242 p hg
    simpa only [d160554, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12244 (p : Pattern) (guard : d160618 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160617 p = 1 := by simpa only [d160618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12238 p hg
    simpa only [d160618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160554 p = 1 := by simpa only [d160618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12243 p hg
    simpa only [d160618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12245 (p : Pattern) (guard : d160619 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160618 p = 1 := by simpa only [d160619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12244 p hg
    simpa only [d160619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12246 (p : Pattern) (guard : d160620 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160619 p = 1 := by simpa only [d160620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12245 p hg
    simpa only [d160620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12247 (p : Pattern) (guard : d160645 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160620 p = 1 := by simpa only [d160645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12246 p hg
    simpa only [d160645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12248 (p : Pattern) (guard : d160555 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160550 p = 1 := by simpa only [d160555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12239 p hg
    simpa only [d160555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12249 (p : Pattern) (guard : d160556 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160555 p = 1 := by simpa only [d160556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12248 p hg
    simpa only [d160556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160556, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
