import NetHack.Soko22Hazard87.Compare041
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10500 (p : Pattern) (guard : d101984 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101983 p = 1 := by simpa only [d101984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10499 p hg
    simpa only [d101984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10501 (p : Pattern) (guard : d101985 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d101964 p = 1 := by simpa only [d101985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10415 p hg
    simpa only [d101985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101984 p = 1 := by simpa only [d101985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10500 p hg
    simpa only [d101985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10502 (p : Pattern) (guard : d10378 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10503 (p : Pattern) (guard : d10379 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10378 p = 1 := by simpa only [d10379, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10502 p hg
    simpa only [d10379, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10379, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d10379, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10504 (p : Pattern) (guard : d10380 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10380, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d10380, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10379 p = 1 := by simpa only [d10380, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10503 p hg
    simpa only [d10380, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10505 (p : Pattern) (guard : d10383 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10506 (p : Pattern) (guard : d10384 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10383 p = 1 := by simpa only [d10384, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10505 p hg
    simpa only [d10384, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10384, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d10384, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10507 (p : Pattern) (guard : d10385 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10385, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d10385, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10384 p = 1 := by simpa only [d10385, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10506 p hg
    simpa only [d10385, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10508 (p : Pattern) (guard : d10386 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d10380 p = 1 := by simpa only [d10386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10504 p hg
    simpa only [d10386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10385 p = 1 := by simpa only [d10386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10507 p hg
    simpa only [d10386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10509 (p : Pattern) (guard : d10398 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10510 (p : Pattern) (guard : d10399 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10398 p = 1 := by simpa only [d10399, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10509 p hg
    simpa only [d10399, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10399, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d10399, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10511 (p : Pattern) (guard : d10400 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10400, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d10400, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10399 p = 1 := by simpa only [d10400, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10510 p hg
    simpa only [d10400, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10512 (p : Pattern) (guard : d10419 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10513 (p : Pattern) (guard : d10420 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10419 p = 1 := by simpa only [d10420, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10512 p hg
    simpa only [d10420, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10420, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d10420, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10514 (p : Pattern) (guard : d10421 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10421, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d10421, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10420 p = 1 := by simpa only [d10421, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10513 p hg
    simpa only [d10421, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10515 (p : Pattern) (guard : d10422 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d10400 p = 1 := by simpa only [d10422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10511 p hg
    simpa only [d10422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10421 p = 1 := by simpa only [d10422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10514 p hg
    simpa only [d10422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10516 (p : Pattern) (guard : d10423 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d10386 p = 1 := by simpa only [d10423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10508 p hg
    simpa only [d10423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10422 p = 1 := by simpa only [d10423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10515 p hg
    simpa only [d10423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10517 (p : Pattern) (guard : d10424 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d10424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10423 p = 1 := by simpa only [d10424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10516 p hg
    simpa only [d10424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10518 (p : Pattern) (guard : d10425 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d10424 p = 1 := by simpa only [d10425, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10517 p hg
    simpa only [d10425, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10425, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d10425, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10519 (p : Pattern) (guard : d10426 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10426, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d10426, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10425 p = 1 := by simpa only [d10426, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10518 p hg
    simpa only [d10426, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10520 (p : Pattern) (guard : d10427 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d10421 p = 1 := by simpa only [d10427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10514 p hg
    simpa only [d10427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d10427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10521 (p : Pattern) (guard : d10428 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d10422 p = 1 := by simpa only [d10428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10515 p hg
    simpa only [d10428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10427 p = 1 := by simpa only [d10428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10520 p hg
    simpa only [d10428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10522 (p : Pattern) (guard : d10429 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d10429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10428 p = 1 := by simpa only [d10429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10521 p hg
    simpa only [d10429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10523 (p : Pattern) (guard : d10430 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d10429 p = 1 := by simpa only [d10430, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10522 p hg
    simpa only [d10430, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10430, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d10430, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10524 (p : Pattern) (guard : d10431 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10431, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d10431, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10430 p = 1 := by simpa only [d10431, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10523 p hg
    simpa only [d10431, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10525 (p : Pattern) (guard : d10432 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d10426 p = 1 := by simpa only [d10432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10519 p hg
    simpa only [d10432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10431 p = 1 := by simpa only [d10432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10524 p hg
    simpa only [d10432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10526 (p : Pattern) (guard : d10433 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d10432 p = 1 := by simpa only [d10433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10525 p hg
    simpa only [d10433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10527 (p : Pattern) (guard : d10434 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d10433 p = 1 := by simpa only [d10434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10526 p hg
    simpa only [d10434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10528 (p : Pattern) (guard : d10435 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d10434 p = 1 := by simpa only [d10435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10527 p hg
    simpa only [d10435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10529 (p : Pattern) (guard : d10441 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10530 (p : Pattern) (guard : d10442 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10441 p = 1 := by simpa only [d10442, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10529 p hg
    simpa only [d10442, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10442, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d10442, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10531 (p : Pattern) (guard : d10443 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10443, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d10443, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10442 p = 1 := by simpa only [d10443, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10530 p hg
    simpa only [d10443, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10532 (p : Pattern) (guard : d10444 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d10443 p = 1 := by simpa only [d10444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10531 p hg
    simpa only [d10444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d10444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10533 (p : Pattern) (guard : d10445 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d10444 p = 1 := by simpa only [d10445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10532 p hg
    simpa only [d10445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d10445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10534 (p : Pattern) (guard : d10446 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d10446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10445 p = 1 := by simpa only [d10446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10533 p hg
    simpa only [d10446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10535 (p : Pattern) (guard : d10447 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d10446 p = 1 := by simpa only [d10447, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10534 p hg
    simpa only [d10447, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10447, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d10447, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10536 (p : Pattern) (guard : d10448 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10448, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d10448, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10447 p = 1 := by simpa only [d10448, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10535 p hg
    simpa only [d10448, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10537 (p : Pattern) (guard : d10449 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d10431 p = 1 := by simpa only [d10449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10524 p hg
    simpa only [d10449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10448 p = 1 := by simpa only [d10449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10536 p hg
    simpa only [d10449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10538 (p : Pattern) (guard : d10450 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d10449 p = 1 := by simpa only [d10450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10537 p hg
    simpa only [d10450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10539 (p : Pattern) (guard : d10451 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d10450 p = 1 := by simpa only [d10451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10538 p hg
    simpa only [d10451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10540 (p : Pattern) (guard : d10452 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d10451 p = 1 := by simpa only [d10452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10539 p hg
    simpa only [d10452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10541 (p : Pattern) (guard : d10453 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d10435 p = 1 := by simpa only [d10453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10528 p hg
    simpa only [d10453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10452 p = 1 := by simpa only [d10453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10540 p hg
    simpa only [d10453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10542 (p : Pattern) (guard : d101986 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d10453 p = 1 := by simpa only [d101986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10541 p hg
    simpa only [d101986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10543 (p : Pattern) (guard : d10560 p = 1) : d47681 p ≤ (1 : Int) + d47681 p := by
  omega
theorem compare10544 (p : Pattern) (guard : d10561 p = 1) : d48273 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10560 p = 1 := by simpa only [d10561, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10543 p hg
    simpa only [d10561, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10561, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10094 p hg
    simpa only [d10561, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10545 (p : Pattern) (guard : d10562 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10562, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10092 p hg
    simpa only [d10562, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10561 p = 1 := by simpa only [d10562, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10544 p hg
    simpa only [d10562, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10546 (p : Pattern) (guard : d10563 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d10562 p = 1 := by simpa only [d10563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10545 p hg
    simpa only [d10563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d10563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10547 (p : Pattern) (guard : d10564 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d10422 p = 1 := by simpa only [d10564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10515 p hg
    simpa only [d10564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10563 p = 1 := by simpa only [d10564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10546 p hg
    simpa only [d10564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10548 (p : Pattern) (guard : d10565 p = 1) : d48274 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10091 p hg
    simpa only [d10565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10564 p = 1 := by simpa only [d10565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10547 p hg
    simpa only [d10565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10549 (p : Pattern) (guard : d10566 p = 1) : d48276 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d10565 p = 1 := by simpa only [d10566, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10548 p hg
    simpa only [d10566, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10566, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10100 p hg
    simpa only [d10566, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10550 (p : Pattern) (guard : d10567 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10567, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10090 p hg
    simpa only [d10567, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10566 p = 1 := by simpa only [d10567, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10549 p hg
    simpa only [d10567, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10551 (p : Pattern) (guard : d10568 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d10567 p = 1 := by simpa only [d10568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10550 p hg
    simpa only [d10568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10552 (p : Pattern) (guard : d10569 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d10568 p = 1 := by simpa only [d10569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10551 p hg
    simpa only [d10569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10553 (p : Pattern) (guard : d10570 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d10569 p = 1 := by simpa only [d10570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10552 p hg
    simpa only [d10570, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10570, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10570, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10554 (p : Pattern) (guard : d10571 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d10570 p = 1 := by simpa only [d10571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10553 p hg
    simpa only [d10571, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10571, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10571, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10555 (p : Pattern) (guard : d10572 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d10571 p = 1 := by simpa only [d10572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10554 p hg
    simpa only [d10572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10556 (p : Pattern) (guard : d10573 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d10572 p = 1 := by simpa only [d10573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10555 p hg
    simpa only [d10573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10557 (p : Pattern) (guard : d101987 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d101986 p = 1 := by simpa only [d101987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10542 p hg
    simpa only [d101987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10573 p = 1 := by simpa only [d101987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10556 p hg
    simpa only [d101987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10558 (p : Pattern) (guard : d101988 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101988, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101987 p = 1 := by simpa only [d101988, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10557 p hg
    simpa only [d101988, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10559 (p : Pattern) (guard : d101989 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d101989, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101988 p = 1 := by simpa only [d101989, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10558 p hg
    simpa only [d101989, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10560 (p : Pattern) (guard : d101990 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101990, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10088 p hg
    simpa only [d101990, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101989 p = 1 := by simpa only [d101990, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10559 p hg
    simpa only [d101990, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10561 (p : Pattern) (guard : d101991 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101991, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101990 p = 1 := by simpa only [d101991, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10560 p hg
    simpa only [d101991, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10562 (p : Pattern) (guard : d10579 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d10448 p = 1 := by simpa only [d10579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10536 p hg
    simpa only [d10579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10563 (p : Pattern) (guard : d10580 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d10579 p = 1 := by simpa only [d10580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10562 p hg
    simpa only [d10580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10564 (p : Pattern) (guard : d10581 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d10580 p = 1 := by simpa only [d10581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10563 p hg
    simpa only [d10581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10565 (p : Pattern) (guard : d10582 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d10581 p = 1 := by simpa only [d10582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10564 p hg
    simpa only [d10582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10566 (p : Pattern) (guard : d10583 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d10582 p = 1 := by simpa only [d10583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10565 p hg
    simpa only [d10583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10567 (p : Pattern) (guard : d10584 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10583 p = 1 := by simpa only [d10584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10566 p hg
    simpa only [d10584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10568 (p : Pattern) (guard : d10585 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d10584 p = 1 := by simpa only [d10585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10567 p hg
    simpa only [d10585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10569 (p : Pattern) (guard : d10586 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10586, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10585 p = 1 := by simpa only [d10586, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10568 p hg
    simpa only [d10586, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10570 (p : Pattern) (guard : d10587 p = 1) : d48277 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10089 p hg
    simpa only [d10587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10586 p = 1 := by simpa only [d10587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10569 p hg
    simpa only [d10587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10571 (p : Pattern) (guard : d10588 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10588, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10088 p hg
    simpa only [d10588, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10587 p = 1 := by simpa only [d10588, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10570 p hg
    simpa only [d10588, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10572 (p : Pattern) (guard : d10589 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d10589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10588 p = 1 := by simpa only [d10589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10571 p hg
    simpa only [d10589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10573 (p : Pattern) (guard : d101992 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d101991 p = 1 := by simpa only [d101992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10561 p hg
    simpa only [d101992, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10589 p = 1 := by simpa only [d101992, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10572 p hg
    simpa only [d101992, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10574 (p : Pattern) (guard : d101993 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d101992 p = 1 := by simpa only [d101993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10573 p hg
    simpa only [d101993, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101993, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101993, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10575 (p : Pattern) (guard : d101994 p = 1) : d48278 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d101993 p = 1 := by simpa only [d101994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10574 p hg
    simpa only [d101994, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101994, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10087 p hg
    simpa only [d101994, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10576 (p : Pattern) (guard : d101995 p = 1) : d48307 p ≤ (1 : Int) + d47910 p := by
  cases selected : p 49 with
  | false =>
    have hg : d101994 p = 1 := by simpa only [d101995, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10575 p hg
    simpa only [d101995, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101995, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10117 p hg
    simpa only [d101995, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10577 (p : Pattern) (guard : d101996 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101996, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10086 p hg
    simpa only [d101996, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101995 p = 1 := by simpa only [d101996, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10576 p hg
    simpa only [d101996, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10578 (p : Pattern) (guard : d101997 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101996 p = 1 := by simpa only [d101997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10577 p hg
    simpa only [d101997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10579 (p : Pattern) (guard : d101998 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101997 p = 1 := by simpa only [d101998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10578 p hg
    simpa only [d101998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10580 (p : Pattern) (guard : d101999 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d101999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d101999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101998 p = 1 := by simpa only [d101999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10579 p hg
    simpa only [d101999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10581 (p : Pattern) (guard : d102000 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101999 p = 1 := by simpa only [d102000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10580 p hg
    simpa only [d102000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10582 (p : Pattern) (guard : d102001 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102000 p = 1 := by simpa only [d102001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10581 p hg
    simpa only [d102001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10583 (p : Pattern) (guard : d102002 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102001 p = 1 := by simpa only [d102002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10582 p hg
    simpa only [d102002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10584 (p : Pattern) (guard : d102003 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102002 p = 1 := by simpa only [d102003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10583 p hg
    simpa only [d102003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10585 (p : Pattern) (guard : d102004 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102003 p = 1 := by simpa only [d102004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10584 p hg
    simpa only [d102004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10586 (p : Pattern) (guard : d102005 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102004 p = 1 := by simpa only [d102005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10585 p hg
    simpa only [d102005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10587 (p : Pattern) (guard : d102006 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102005 p = 1 := by simpa only [d102006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10586 p hg
    simpa only [d102006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10588 (p : Pattern) (guard : d102007 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d101985 p = 1 := by simpa only [d102007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10501 p hg
    simpa only [d102007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102006 p = 1 := by simpa only [d102007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10587 p hg
    simpa only [d102007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10589 (p : Pattern) (guard : d102008 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 260 with
  | false =>
    have hg : d102007 p = 1 := by simpa only [d102008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10588 p hg
    simpa only [d102008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10590 (p : Pattern) (guard : d102009 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 259 with
  | false =>
    have hg : d102008 p = 1 := by simpa only [d102009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10589 p hg
    simpa only [d102009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10591 (p : Pattern) (guard : d102010 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 258 with
  | false =>
    have hg : d102009 p = 1 := by simpa only [d102010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10590 p hg
    simpa only [d102010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10592 (p : Pattern) (guard : d102011 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 257 with
  | false =>
    have hg : d102010 p = 1 := by simpa only [d102011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10591 p hg
    simpa only [d102011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10593 (p : Pattern) (guard : d102012 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 256 with
  | false =>
    have hg : d102011 p = 1 := by simpa only [d102012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10592 p hg
    simpa only [d102012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10594 (p : Pattern) (guard : d102013 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 255 with
  | false =>
    have hg : d102012 p = 1 := by simpa only [d102013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10593 p hg
    simpa only [d102013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10595 (p : Pattern) (guard : d102014 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 254 with
  | false =>
    have hg : d102013 p = 1 := by simpa only [d102014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10594 p hg
    simpa only [d102014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10596 (p : Pattern) (guard : d102015 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 253 with
  | false =>
    have hg : d102014 p = 1 := by simpa only [d102015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10595 p hg
    simpa only [d102015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10597 (p : Pattern) (guard : d102016 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 252 with
  | false =>
    have hg : d102015 p = 1 := by simpa only [d102016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10596 p hg
    simpa only [d102016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10598 (p : Pattern) (guard : d102017 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 251 with
  | false =>
    have hg : d102016 p = 1 := by simpa only [d102017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10597 p hg
    simpa only [d102017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10599 (p : Pattern) (guard : d102018 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 250 with
  | false =>
    have hg : d102017 p = 1 := by simpa only [d102018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10598 p hg
    simpa only [d102018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10600 (p : Pattern) (guard : d102019 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 249 with
  | false =>
    have hg : d102018 p = 1 := by simpa only [d102019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10599 p hg
    simpa only [d102019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10601 (p : Pattern) (guard : d102020 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 245 with
  | false =>
    have hg : d102019 p = 1 := by simpa only [d102020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10600 p hg
    simpa only [d102020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10602 (p : Pattern) (guard : d102021 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 200 with
  | false =>
    have hg : d102020 p = 1 := by simpa only [d102021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10601 p hg
    simpa only [d102021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10603 (p : Pattern) (guard : d102022 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 199 with
  | false =>
    have hg : d102021 p = 1 := by simpa only [d102022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10602 p hg
    simpa only [d102022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10604 (p : Pattern) (guard : d102023 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 186 with
  | false =>
    have hg : d102022 p = 1 := by simpa only [d102023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10603 p hg
    simpa only [d102023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10605 (p : Pattern) (guard : d102024 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 185 with
  | false =>
    have hg : d102023 p = 1 := by simpa only [d102024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10604 p hg
    simpa only [d102024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10606 (p : Pattern) (guard : d102025 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 184 with
  | false =>
    have hg : d102024 p = 1 := by simpa only [d102025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10605 p hg
    simpa only [d102025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10607 (p : Pattern) (guard : d102026 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 181 with
  | false =>
    have hg : d102025 p = 1 := by simpa only [d102026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10606 p hg
    simpa only [d102026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10608 (p : Pattern) (guard : d102027 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 177 with
  | false =>
    have hg : d102026 p = 1 := by simpa only [d102027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10607 p hg
    simpa only [d102027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10609 (p : Pattern) (guard : d102028 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 164 with
  | false =>
    have hg : d102027 p = 1 := by simpa only [d102028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10608 p hg
    simpa only [d102028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10610 (p : Pattern) (guard : d102029 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 156 with
  | false =>
    have hg : d102028 p = 1 := by simpa only [d102029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10609 p hg
    simpa only [d102029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10611 (p : Pattern) (guard : d102030 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 155 with
  | false =>
    have hg : d102029 p = 1 := by simpa only [d102030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10610 p hg
    simpa only [d102030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10612 (p : Pattern) (guard : d102031 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 134 with
  | false =>
    have hg : d102030 p = 1 := by simpa only [d102031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10611 p hg
    simpa only [d102031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10613 (p : Pattern) (guard : d102032 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 133 with
  | false =>
    have hg : d102031 p = 1 := by simpa only [d102032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10612 p hg
    simpa only [d102032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10614 (p : Pattern) (guard : d102033 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 120 with
  | false =>
    have hg : d102032 p = 1 := by simpa only [d102033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10613 p hg
    simpa only [d102033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10615 (p : Pattern) (guard : d102034 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 118 with
  | false =>
    have hg : d102033 p = 1 := by simpa only [d102034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10614 p hg
    simpa only [d102034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10616 (p : Pattern) (guard : d102035 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 114 with
  | false =>
    have hg : d102034 p = 1 := by simpa only [d102035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10615 p hg
    simpa only [d102035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10617 (p : Pattern) (guard : d102036 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 111 with
  | false =>
    have hg : d102035 p = 1 := by simpa only [d102036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10616 p hg
    simpa only [d102036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10618 (p : Pattern) (guard : d102037 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 98 with
  | false =>
    have hg : d102036 p = 1 := by simpa only [d102037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10617 p hg
    simpa only [d102037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10619 (p : Pattern) (guard : d102038 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 97 with
  | false =>
    have hg : d102037 p = 1 := by simpa only [d102038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10618 p hg
    simpa only [d102038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10620 (p : Pattern) (guard : d102039 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 94 with
  | false =>
    have hg : d102038 p = 1 := by simpa only [d102039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10619 p hg
    simpa only [d102039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10621 (p : Pattern) (guard : d102040 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 76 with
  | false =>
    have hg : d102039 p = 1 := by simpa only [d102040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10620 p hg
    simpa only [d102040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10622 (p : Pattern) (guard : d102041 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 67 with
  | false =>
    have hg : d102040 p = 1 := by simpa only [d102041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10621 p hg
    simpa only [d102041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10623 (p : Pattern) (guard : d102042 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 52 with
  | false =>
    have hg : d102041 p = 1 := by simpa only [d102042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10622 p hg
    simpa only [d102042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10624 (p : Pattern) (guard : d102043 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 47 with
  | false =>
    have hg : d102042 p = 1 := by simpa only [d102043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10623 p hg
    simpa only [d102043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10625 (p : Pattern) (guard : d102044 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 46 with
  | false =>
    have hg : d102043 p = 1 := by simpa only [d102044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10624 p hg
    simpa only [d102044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10626 (p : Pattern) (guard : d102045 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 45 with
  | false =>
    have hg : d102044 p = 1 := by simpa only [d102045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10625 p hg
    simpa only [d102045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10627 (p : Pattern) (guard : d102046 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 30 with
  | false =>
    have hg : d102045 p = 1 := by simpa only [d102046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10626 p hg
    simpa only [d102046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10628 (p : Pattern) (guard : d102047 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 29 with
  | false =>
    have hg : d102046 p = 1 := by simpa only [d102047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10627 p hg
    simpa only [d102047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10629 (p : Pattern) (guard : d102048 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 28 with
  | false =>
    have hg : d102047 p = 1 := by simpa only [d102048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10628 p hg
    simpa only [d102048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10630 (p : Pattern) (guard : d102049 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 27 with
  | false =>
    have hg : d102048 p = 1 := by simpa only [d102049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10629 p hg
    simpa only [d102049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10631 (p : Pattern) (guard : d102050 p = 1) : d48308 p ≤ (1 : Int) + d47911 p := by
  cases selected : p 25 with
  | false =>
    have hg : d102049 p = 1 := by simpa only [d102050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10630 p hg
    simpa only [d102050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d102050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10085 p hg
    simpa only [d102050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10632 (p : Pattern) (guard : d0 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10633 (p : Pattern) (guard : d0 p = 1) : d48293 p ≤ (0 : Int) + d47768 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10634 (p : Pattern) (guard : d0 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10635 (p : Pattern) (guard : d0 p = 1) : d48265 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10636 (p : Pattern) (guard : d0 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10637 (p : Pattern) (guard : d0 p = 1) : d48271 p ≤ (0 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10638 (p : Pattern) (guard : d0 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10639 (p : Pattern) (guard : d0 p = 1) : d48272 p ≤ (0 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10640 (p : Pattern) (guard : d9297 p = 1) : d47681 p ≤ (0 : Int) + d47681 p := by
  omega
theorem compare10641 (p : Pattern) (guard : d0 p = 1) : d48010 p ≤ (0 : Int) + d47685 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10642 (p : Pattern) (guard : d9298 p = 1) : d48273 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9297 p = 1 := by simpa only [d9298, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10640 p hg
    simpa only [d9298, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9298, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10641 p hg
    simpa only [d9298, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10643 (p : Pattern) (guard : d9299 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9299, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10639 p hg
    simpa only [d9299, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9298 p = 1 := by simpa only [d9299, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10642 p hg
    simpa only [d9299, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10644 (p : Pattern) (guard : d9300 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9299 p = 1 := by simpa only [d9300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10643 p hg
    simpa only [d9300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d9300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10645 (p : Pattern) (guard : d9301 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9300 p = 1 := by simpa only [d9301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10644 p hg
    simpa only [d9301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d9301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10646 (p : Pattern) (guard : d9302 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d9302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9301 p = 1 := by simpa only [d9302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10645 p hg
    simpa only [d9302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10647 (p : Pattern) (guard : d0 p = 1) : d48275 p ≤ (0 : Int) + d47698 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10648 (p : Pattern) (guard : d9303 p = 1) : d48276 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9302 p = 1 := by simpa only [d9303, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10646 p hg
    simpa only [d9303, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9303, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10647 p hg
    simpa only [d9303, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10649 (p : Pattern) (guard : d9304 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9304, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10637 p hg
    simpa only [d9304, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9303 p = 1 := by simpa only [d9304, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10648 p hg
    simpa only [d9304, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10650 (p : Pattern) (guard : d9305 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9304 p = 1 := by simpa only [d9305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10649 p hg
    simpa only [d9305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10651 (p : Pattern) (guard : d9306 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9305 p = 1 := by simpa only [d9306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10650 p hg
    simpa only [d9306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10652 (p : Pattern) (guard : d9307 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9306 p = 1 := by simpa only [d9307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10651 p hg
    simpa only [d9307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10653 (p : Pattern) (guard : d9308 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9307 p = 1 := by simpa only [d9308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10652 p hg
    simpa only [d9308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10654 (p : Pattern) (guard : d9309 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d9308 p = 1 := by simpa only [d9309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10653 p hg
    simpa only [d9309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10655 (p : Pattern) (guard : d9432 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9309 p = 1 := by simpa only [d9432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10654 p hg
    simpa only [d9432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10656 (p : Pattern) (guard : d9433 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d9432 p = 1 := by simpa only [d9433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10655 p hg
    simpa only [d9433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10657 (p : Pattern) (guard : d9434 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9433 p = 1 := by simpa only [d9434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10656 p hg
    simpa only [d9434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10658 (p : Pattern) (guard : d9435 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9434 p = 1 := by simpa only [d9435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10657 p hg
    simpa only [d9435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10659 (p : Pattern) (guard : d9436 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9436, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10635 p hg
    simpa only [d9436, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9435 p = 1 := by simpa only [d9436, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10658 p hg
    simpa only [d9436, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10660 (p : Pattern) (guard : d9437 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d9437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9436 p = 1 := by simpa only [d9437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10659 p hg
    simpa only [d9437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10661 (p : Pattern) (guard : d129473 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d9437 p = 1 := by simpa only [d129473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10660 p hg
    simpa only [d129473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10662 (p : Pattern) (guard : d129474 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d129473 p = 1 := by simpa only [d129474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10661 p hg
    simpa only [d129474, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129474, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129474, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10663 (p : Pattern) (guard : d129475 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d129474 p = 1 := by simpa only [d129475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10662 p hg
    simpa only [d129475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10664 (p : Pattern) (guard : d0 p = 1) : d48306 p ≤ (0 : Int) + d47909 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10665 (p : Pattern) (guard : d129476 p = 1) : d48307 p ≤ (0 : Int) + d47910 p := by
  cases selected : p 49 with
  | false =>
    have hg : d129475 p = 1 := by simpa only [d129476, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10663 p hg
    simpa only [d129476, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129476, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10664 p hg
    simpa only [d129476, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10666 (p : Pattern) (guard : d129477 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129477, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10633 p hg
    simpa only [d129477, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129476 p = 1 := by simpa only [d129477, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10665 p hg
    simpa only [d129477, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10667 (p : Pattern) (guard : d129478 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129478, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129477 p = 1 := by simpa only [d129478, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10666 p hg
    simpa only [d129478, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10668 (p : Pattern) (guard : d129479 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129478 p = 1 := by simpa only [d129479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10667 p hg
    simpa only [d129479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10669 (p : Pattern) (guard : d129480 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129479 p = 1 := by simpa only [d129480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10668 p hg
    simpa only [d129480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10670 (p : Pattern) (guard : d129481 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129480 p = 1 := by simpa only [d129481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10669 p hg
    simpa only [d129481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10671 (p : Pattern) (guard : d129482 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129482, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129481 p = 1 := by simpa only [d129482, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10670 p hg
    simpa only [d129482, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10672 (p : Pattern) (guard : d9330 p = 1) : d47681 p ≤ (0 : Int) + d47681 p := by
  omega
theorem compare10673 (p : Pattern) (guard : d9331 p = 1) : d48273 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9330 p = 1 := by simpa only [d9331, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10672 p hg
    simpa only [d9331, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9331, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10641 p hg
    simpa only [d9331, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10674 (p : Pattern) (guard : d9332 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9332, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10639 p hg
    simpa only [d9332, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9331 p = 1 := by simpa only [d9332, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10673 p hg
    simpa only [d9332, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10675 (p : Pattern) (guard : d9333 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9332 p = 1 := by simpa only [d9333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10674 p hg
    simpa only [d9333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9299 p = 1 := by simpa only [d9333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10643 p hg
    simpa only [d9333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10676 (p : Pattern) (guard : d9334 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9333 p = 1 := by simpa only [d9334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10675 p hg
    simpa only [d9334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9300 p = 1 := by simpa only [d9334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10644 p hg
    simpa only [d9334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10677 (p : Pattern) (guard : d9335 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d9335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9334 p = 1 := by simpa only [d9335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10676 p hg
    simpa only [d9335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10678 (p : Pattern) (guard : d9336 p = 1) : d48276 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9335 p = 1 := by simpa only [d9336, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10677 p hg
    simpa only [d9336, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9336, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10647 p hg
    simpa only [d9336, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10679 (p : Pattern) (guard : d9337 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9337, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10637 p hg
    simpa only [d9337, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9336 p = 1 := by simpa only [d9337, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10678 p hg
    simpa only [d9337, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10680 (p : Pattern) (guard : d9338 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9337 p = 1 := by simpa only [d9338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10679 p hg
    simpa only [d9338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9304 p = 1 := by simpa only [d9338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10649 p hg
    simpa only [d9338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10681 (p : Pattern) (guard : d9339 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9338 p = 1 := by simpa only [d9339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10680 p hg
    simpa only [d9339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10682 (p : Pattern) (guard : d9340 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9339 p = 1 := by simpa only [d9340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10681 p hg
    simpa only [d9340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10683 (p : Pattern) (guard : d9341 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9340 p = 1 := by simpa only [d9341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10682 p hg
    simpa only [d9341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10684 (p : Pattern) (guard : d9342 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d9341 p = 1 := by simpa only [d9342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10683 p hg
    simpa only [d9342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9308 p = 1 := by simpa only [d9342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10653 p hg
    simpa only [d9342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10685 (p : Pattern) (guard : d129483 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129483, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9342 p = 1 := by simpa only [d129483, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10684 p hg
    simpa only [d129483, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10686 (p : Pattern) (guard : d129484 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d129483 p = 1 := by simpa only [d129484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10685 p hg
    simpa only [d129484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10687 (p : Pattern) (guard : d129485 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129484 p = 1 := by simpa only [d129485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10686 p hg
    simpa only [d129485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10688 (p : Pattern) (guard : d129486 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129485 p = 1 := by simpa only [d129486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10687 p hg
    simpa only [d129486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10689 (p : Pattern) (guard : d129487 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129487, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10635 p hg
    simpa only [d129487, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129486 p = 1 := by simpa only [d129487, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10688 p hg
    simpa only [d129487, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10690 (p : Pattern) (guard : d129488 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129487 p = 1 := by simpa only [d129488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10689 p hg
    simpa only [d129488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10691 (p : Pattern) (guard : d129489 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d129488 p = 1 := by simpa only [d129489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10690 p hg
    simpa only [d129489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10692 (p : Pattern) (guard : d129490 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d129489 p = 1 := by simpa only [d129490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10691 p hg
    simpa only [d129490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10693 (p : Pattern) (guard : d129491 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d129490 p = 1 := by simpa only [d129491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10692 p hg
    simpa only [d129491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10694 (p : Pattern) (guard : d129492 p = 1) : d48307 p ≤ (0 : Int) + d47910 p := by
  cases selected : p 49 with
  | false =>
    have hg : d129491 p = 1 := by simpa only [d129492, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10693 p hg
    simpa only [d129492, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129492, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10664 p hg
    simpa only [d129492, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10695 (p : Pattern) (guard : d129493 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129493, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10633 p hg
    simpa only [d129493, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129492 p = 1 := by simpa only [d129493, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10694 p hg
    simpa only [d129493, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10696 (p : Pattern) (guard : d129494 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129493 p = 1 := by simpa only [d129494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10695 p hg
    simpa only [d129494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10697 (p : Pattern) (guard : d129495 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129494 p = 1 := by simpa only [d129495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10696 p hg
    simpa only [d129495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10698 (p : Pattern) (guard : d129496 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129495 p = 1 := by simpa only [d129496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10697 p hg
    simpa only [d129496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10699 (p : Pattern) (guard : d129497 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129496 p = 1 := by simpa only [d129497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10698 p hg
    simpa only [d129497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10700 (p : Pattern) (guard : d129498 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129497 p = 1 := by simpa only [d129498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10699 p hg
    simpa only [d129498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10701 (p : Pattern) (guard : d129499 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d129482 p = 1 := by simpa only [d129499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10671 p hg
    simpa only [d129499, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129498 p = 1 := by simpa only [d129499, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10700 p hg
    simpa only [d129499, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10702 (p : Pattern) (guard : d9389 p = 1) : d47681 p ≤ (0 : Int) + d47681 p := by
  omega
theorem compare10703 (p : Pattern) (guard : d9390 p = 1) : d48273 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9389 p = 1 := by simpa only [d9390, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10702 p hg
    simpa only [d9390, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9390, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10641 p hg
    simpa only [d9390, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10704 (p : Pattern) (guard : d9391 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9391, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10639 p hg
    simpa only [d9391, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9390 p = 1 := by simpa only [d9391, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10703 p hg
    simpa only [d9391, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10705 (p : Pattern) (guard : d9392 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9391 p = 1 := by simpa only [d9392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10704 p hg
    simpa only [d9392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9332 p = 1 := by simpa only [d9392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10674 p hg
    simpa only [d9392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10706 (p : Pattern) (guard : d9487 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9332 p = 1 := by simpa only [d9487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10674 p hg
    simpa only [d9487, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9487, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d9487, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10707 (p : Pattern) (guard : d9488 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9392 p = 1 := by simpa only [d9488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10705 p hg
    simpa only [d9488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9487 p = 1 := by simpa only [d9488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10706 p hg
    simpa only [d9488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10708 (p : Pattern) (guard : d9489 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d9489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9488 p = 1 := by simpa only [d9489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10707 p hg
    simpa only [d9489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10709 (p : Pattern) (guard : d9490 p = 1) : d48276 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9489 p = 1 := by simpa only [d9490, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10708 p hg
    simpa only [d9490, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9490, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10647 p hg
    simpa only [d9490, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10710 (p : Pattern) (guard : d9491 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9491, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10637 p hg
    simpa only [d9491, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9490 p = 1 := by simpa only [d9491, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10709 p hg
    simpa only [d9491, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10711 (p : Pattern) (guard : d9496 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9487 p = 1 := by simpa only [d9496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10706 p hg
    simpa only [d9496, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9496, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d9496, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10712 (p : Pattern) (guard : d9497 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d9497, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9496 p = 1 := by simpa only [d9497, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10711 p hg
    simpa only [d9497, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10713 (p : Pattern) (guard : d9498 p = 1) : d48276 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9497 p = 1 := by simpa only [d9498, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10712 p hg
    simpa only [d9498, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9498, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10647 p hg
    simpa only [d9498, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10714 (p : Pattern) (guard : d9499 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9499, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10637 p hg
    simpa only [d9499, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9498 p = 1 := by simpa only [d9499, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10713 p hg
    simpa only [d9499, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10715 (p : Pattern) (guard : d9500 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9491 p = 1 := by simpa only [d9500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10710 p hg
    simpa only [d9500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9499 p = 1 := by simpa only [d9500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10714 p hg
    simpa only [d9500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10716 (p : Pattern) (guard : d9501 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9500 p = 1 := by simpa only [d9501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10715 p hg
    simpa only [d9501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10717 (p : Pattern) (guard : d9502 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9501 p = 1 := by simpa only [d9502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10716 p hg
    simpa only [d9502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10718 (p : Pattern) (guard : d9503 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9502 p = 1 := by simpa only [d9503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10717 p hg
    simpa only [d9503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10719 (p : Pattern) (guard : d9553 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9499 p = 1 := by simpa only [d9553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10714 p hg
    simpa only [d9553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10720 (p : Pattern) (guard : d9554 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9553 p = 1 := by simpa only [d9554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10719 p hg
    simpa only [d9554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10721 (p : Pattern) (guard : d9555 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9554 p = 1 := by simpa only [d9555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10720 p hg
    simpa only [d9555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10722 (p : Pattern) (guard : d9556 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9555 p = 1 := by simpa only [d9556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10721 p hg
    simpa only [d9556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10723 (p : Pattern) (guard : d129500 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d9503 p = 1 := by simpa only [d129500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10718 p hg
    simpa only [d129500, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9556 p = 1 := by simpa only [d129500, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10722 p hg
    simpa only [d129500, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10724 (p : Pattern) (guard : d129501 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129500 p = 1 := by simpa only [d129501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10723 p hg
    simpa only [d129501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10725 (p : Pattern) (guard : d129502 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d129501 p = 1 := by simpa only [d129502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10724 p hg
    simpa only [d129502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10726 (p : Pattern) (guard : d129503 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129502 p = 1 := by simpa only [d129503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10725 p hg
    simpa only [d129503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10727 (p : Pattern) (guard : d129504 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129503 p = 1 := by simpa only [d129504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10726 p hg
    simpa only [d129504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10728 (p : Pattern) (guard : d129505 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129505, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10635 p hg
    simpa only [d129505, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129504 p = 1 := by simpa only [d129505, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10727 p hg
    simpa only [d129505, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10729 (p : Pattern) (guard : d129506 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129505 p = 1 := by simpa only [d129506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10728 p hg
    simpa only [d129506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10730 (p : Pattern) (guard : d129507 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d129506 p = 1 := by simpa only [d129507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10729 p hg
    simpa only [d129507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10731 (p : Pattern) (guard : d129508 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d129507 p = 1 := by simpa only [d129508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10730 p hg
    simpa only [d129508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10732 (p : Pattern) (guard : d129509 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d129508 p = 1 := by simpa only [d129509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10731 p hg
    simpa only [d129509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10733 (p : Pattern) (guard : d129510 p = 1) : d48307 p ≤ (0 : Int) + d47910 p := by
  cases selected : p 49 with
  | false =>
    have hg : d129509 p = 1 := by simpa only [d129510, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10732 p hg
    simpa only [d129510, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129510, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10664 p hg
    simpa only [d129510, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10734 (p : Pattern) (guard : d129511 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129511, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10633 p hg
    simpa only [d129511, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129510 p = 1 := by simpa only [d129511, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10733 p hg
    simpa only [d129511, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10735 (p : Pattern) (guard : d129512 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129511 p = 1 := by simpa only [d129512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10734 p hg
    simpa only [d129512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10736 (p : Pattern) (guard : d129513 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129513, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129512 p = 1 := by simpa only [d129513, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10735 p hg
    simpa only [d129513, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10737 (p : Pattern) (guard : d129514 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129514, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129513 p = 1 := by simpa only [d129514, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10736 p hg
    simpa only [d129514, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10738 (p : Pattern) (guard : d129515 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129514 p = 1 := by simpa only [d129515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10737 p hg
    simpa only [d129515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10739 (p : Pattern) (guard : d129516 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129515 p = 1 := by simpa only [d129516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10738 p hg
    simpa only [d129516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10740 (p : Pattern) (guard : d129517 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129516 p = 1 := by simpa only [d129517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10739 p hg
    simpa only [d129517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10741 (p : Pattern) (guard : d129518 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d129499 p = 1 := by simpa only [d129518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10701 p hg
    simpa only [d129518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129517 p = 1 := by simpa only [d129518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10740 p hg
    simpa only [d129518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10742 (p : Pattern) (guard : d9620 p = 1) : d47681 p ≤ (0 : Int) + d47681 p := by
  omega
theorem compare10743 (p : Pattern) (guard : d9621 p = 1) : d48273 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9620 p = 1 := by simpa only [d9621, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10742 p hg
    simpa only [d9621, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9621, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10641 p hg
    simpa only [d9621, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10744 (p : Pattern) (guard : d9622 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9622, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10639 p hg
    simpa only [d9622, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9621 p = 1 := by simpa only [d9622, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10743 p hg
    simpa only [d9622, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10745 (p : Pattern) (guard : d9624 p = 1) : d47681 p ≤ (0 : Int) + d47681 p := by
  omega
theorem compare10746 (p : Pattern) (guard : d9625 p = 1) : d48273 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9624 p = 1 := by simpa only [d9625, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10745 p hg
    simpa only [d9625, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9625, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10641 p hg
    simpa only [d9625, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10747 (p : Pattern) (guard : d9626 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9626, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10639 p hg
    simpa only [d9626, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9625 p = 1 := by simpa only [d9626, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10746 p hg
    simpa only [d9626, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10748 (p : Pattern) (guard : d9627 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9622 p = 1 := by simpa only [d9627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10744 p hg
    simpa only [d9627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9626 p = 1 := by simpa only [d9627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10747 p hg
    simpa only [d9627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10749 (p : Pattern) (guard : d9632 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9626 p = 1 := by simpa only [d9632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10747 p hg
    simpa only [d9632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d9632, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
