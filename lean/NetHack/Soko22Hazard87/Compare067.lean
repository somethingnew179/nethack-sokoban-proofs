import NetHack.Soko22Hazard87.Compare066
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare16750 (p : Pattern) (guard : d15968 p = 1) : d48326 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15968, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16499 p hg
    simpa only [d15968, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15967 p = 1 := by simpa only [d15968, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16749 p hg
    simpa only [d15968, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16751 (p : Pattern) (guard : d15969 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15969, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d15969, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15968 p = 1 := by simpa only [d15969, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16750 p hg
    simpa only [d15969, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16752 (p : Pattern) (guard : d15970 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d15969 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16751 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16639 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16753 (p : Pattern) (guard : d475 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16639 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16754 (p : Pattern) (guard : d16035 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16752 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16753 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16755 (p : Pattern) (guard : d16036 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16035 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16754 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16756 (p : Pattern) (guard : d16037 p = 1) : d48338 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16036 p = 1 := by simpa only [d16037, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16755 p hg
    simpa only [d16037, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16037, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d16037, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16757 (p : Pattern) (guard : d16038 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16038, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d16038, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16037 p = 1 := by simpa only [d16038, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16756 p hg
    simpa only [d16038, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16758 (p : Pattern) (guard : d480 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16753 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16759 (p : Pattern) (guard : d481 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16758 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16760 (p : Pattern) (guard : d482 p = 1) : d48338 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16759 p hg
    simpa only [d482, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d482, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16761 (p : Pattern) (guard : d483 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d483, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16760 p hg
    simpa only [d483, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16762 (p : Pattern) (guard : d16039 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16757 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16761 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16763 (p : Pattern) (guard : d16040 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16039 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16762 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16764 (p : Pattern) (guard : d16041 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16040 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16763 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16765 (p : Pattern) (guard : d16042 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16041 p = 1 := by simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16764 p hg
    simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16766 (p : Pattern) (guard : d488 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16761 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16767 (p : Pattern) (guard : d489 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16766 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16768 (p : Pattern) (guard : d490 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16767 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16769 (p : Pattern) (guard : d491 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d490 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16768 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16770 (p : Pattern) (guard : d16043 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16042 p = 1 := by simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16765 p hg
    simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d491 p = 1 := by simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16769 p hg
    simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16771 (p : Pattern) (guard : d16044 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16043 p = 1 := by simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16770 p hg
    simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16772 (p : Pattern) (guard : d16045 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16044 p = 1 := by simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16771 p hg
    simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16773 (p : Pattern) (guard : d16046 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16045 p = 1 := by simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16772 p hg
    simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16774 (p : Pattern) (guard : d16047 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16046 p = 1 := by simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16773 p hg
    simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16775 (p : Pattern) (guard : d16048 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16048, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16048, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16047 p = 1 := by simpa only [d16048, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16774 p hg
    simpa only [d16048, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16776 (p : Pattern) (guard : d15969 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15969, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16527 p hg
    simpa only [d15969, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15968 p = 1 := by simpa only [d15969, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16750 p hg
    simpa only [d15969, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16777 (p : Pattern) (guard : d15970 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d15969 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16776 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16655 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16778 (p : Pattern) (guard : d475 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16655 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16779 (p : Pattern) (guard : d16035 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16777 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16778 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16780 (p : Pattern) (guard : d16036 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16035 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16779 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16781 (p : Pattern) (guard : d16037 p = 1) : d48329 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16036 p = 1 := by simpa only [d16037, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16780 p hg
    simpa only [d16037, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16037, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d16037, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16782 (p : Pattern) (guard : d16038 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16038, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16526 p hg
    simpa only [d16038, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16037 p = 1 := by simpa only [d16038, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16781 p hg
    simpa only [d16038, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16783 (p : Pattern) (guard : d480 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16778 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16784 (p : Pattern) (guard : d481 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16783 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16785 (p : Pattern) (guard : d482 p = 1) : d48329 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16784 p hg
    simpa only [d482, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d482, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16786 (p : Pattern) (guard : d483 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16526 p hg
    simpa only [d483, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16785 p hg
    simpa only [d483, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16787 (p : Pattern) (guard : d16039 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16782 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16786 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16788 (p : Pattern) (guard : d16040 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16039 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16787 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16789 (p : Pattern) (guard : d16041 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16040 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16788 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16790 (p : Pattern) (guard : d16042 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16041 p = 1 := by simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16789 p hg
    simpa only [d16042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16791 (p : Pattern) (guard : d488 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16786 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16792 (p : Pattern) (guard : d489 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16791 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16793 (p : Pattern) (guard : d490 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16792 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16794 (p : Pattern) (guard : d491 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d490 p = 1 := by simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16793 p hg
    simpa only [d491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16795 (p : Pattern) (guard : d16043 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16042 p = 1 := by simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16790 p hg
    simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d491 p = 1 := by simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16794 p hg
    simpa only [d16043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16796 (p : Pattern) (guard : d16044 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16043 p = 1 := by simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16795 p hg
    simpa only [d16044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16797 (p : Pattern) (guard : d16045 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16044 p = 1 := by simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16796 p hg
    simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16798 (p : Pattern) (guard : d16046 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16045 p = 1 := by simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16797 p hg
    simpa only [d16046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16799 (p : Pattern) (guard : d16047 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16046 p = 1 := by simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16798 p hg
    simpa only [d16047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16800 (p : Pattern) (guard : d16051 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16041 p = 1 := by simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16764 p hg
    simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16801 (p : Pattern) (guard : d501 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d490 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16768 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16802 (p : Pattern) (guard : d16052 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16051 p = 1 := by simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16800 p hg
    simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d501 p = 1 := by simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16801 p hg
    simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16803 (p : Pattern) (guard : d16053 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16052 p = 1 := by simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16802 p hg
    simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16804 (p : Pattern) (guard : d16054 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16053 p = 1 := by simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16803 p hg
    simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16805 (p : Pattern) (guard : d16055 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16054 p = 1 := by simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16804 p hg
    simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16806 (p : Pattern) (guard : d16056 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16055 p = 1 := by simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16805 p hg
    simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16807 (p : Pattern) (guard : d16057 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16047 p = 1 := by simpa only [d16057, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16799 p hg
    simpa only [d16057, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16056 p = 1 := by simpa only [d16057, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16806 p hg
    simpa only [d16057, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16808 (p : Pattern) (guard : d16058 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16048 p = 1 := by simpa only [d16058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16775 p hg
    simpa only [d16058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16057 p = 1 := by simpa only [d16058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16807 p hg
    simpa only [d16058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16809 (p : Pattern) (guard : d16059 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16058 p = 1 := by simpa only [d16059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16808 p hg
    simpa only [d16059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d16059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16810 (p : Pattern) (guard : d171076 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d16059 p = 1 := by simpa only [d171076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16809 p hg
    simpa only [d171076, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171076, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d171076, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16811 (p : Pattern) (guard : d171077 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d171077, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171076 p = 1 := by simpa only [d171077, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16810 p hg
    simpa only [d171077, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16812 (p : Pattern) (guard : d321 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare16813 (p : Pattern) (guard : d322 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d321 p = 1 := by simpa only [d322, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16812 p hg
    simpa only [d322, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d322, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d322, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16814 (p : Pattern) (guard : d323 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16813 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16682 p hg
    simpa only [d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16815 (p : Pattern) (guard : d12493 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare16816 (p : Pattern) (guard : d12494 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12493 p = 1 := by simpa only [d12494, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16815 p hg
    simpa only [d12494, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12494, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d12494, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16817 (p : Pattern) (guard : d12495 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12494 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16816 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16562 p hg
    simpa only [d12495, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16818 (p : Pattern) (guard : d15966 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d323 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16814 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12495 p = 1 := by simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16817 p hg
    simpa only [d15966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16819 (p : Pattern) (guard : d15967 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d15966 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16818 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d144 p = 1 := by simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16684 p hg
    simpa only [d15967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16820 (p : Pattern) (guard : d15968 p = 1) : d48346 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15968, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16559 p hg
    simpa only [d15968, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15967 p = 1 := by simpa only [d15968, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16819 p hg
    simpa only [d15968, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16821 (p : Pattern) (guard : d15969 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d15969, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16558 p hg
    simpa only [d15969, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15968 p = 1 := by simpa only [d15969, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16820 p hg
    simpa only [d15969, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16822 (p : Pattern) (guard : d15970 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d15969 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16821 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d147 p = 1 := by simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16687 p hg
    simpa only [d15970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16823 (p : Pattern) (guard : d475 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d147 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16687 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d475, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16824 (p : Pattern) (guard : d16035 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d15970 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16822 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d475 p = 1 := by simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16823 p hg
    simpa only [d16035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16825 (p : Pattern) (guard : d16036 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16035 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16824 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d16036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16826 (p : Pattern) (guard : d16037 p = 1) : d48356 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16036 p = 1 := by simpa only [d16037, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16825 p hg
    simpa only [d16037, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16037, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16573 p hg
    simpa only [d16037, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16827 (p : Pattern) (guard : d16038 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16038, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16557 p hg
    simpa only [d16038, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16037 p = 1 := by simpa only [d16038, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16826 p hg
    simpa only [d16038, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16828 (p : Pattern) (guard : d480 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d475 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16823 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16829 (p : Pattern) (guard : d481 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d480 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16828 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16569 p hg
    simpa only [d481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16830 (p : Pattern) (guard : d482 p = 1) : d48356 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d481 p = 1 := by simpa only [d482, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16829 p hg
    simpa only [d482, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d482, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16573 p hg
    simpa only [d482, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16831 (p : Pattern) (guard : d483 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d483, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16557 p hg
    simpa only [d483, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d482 p = 1 := by simpa only [d483, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16830 p hg
    simpa only [d483, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16832 (p : Pattern) (guard : d16039 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16038 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16827 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d483 p = 1 := by simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16831 p hg
    simpa only [d16039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16833 (p : Pattern) (guard : d16040 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16039 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16832 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16834 (p : Pattern) (guard : d16041 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16040 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16833 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16835 (p : Pattern) (guard : d16051 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16041 p = 1 := by simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16834 p hg
    simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16836 (p : Pattern) (guard : d488 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d483 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16831 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16837 (p : Pattern) (guard : d489 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d488 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16836 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16838 (p : Pattern) (guard : d490 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d489 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16837 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16839 (p : Pattern) (guard : d501 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 93 with
  | false =>
    have hg : d490 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16838 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d501, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16840 (p : Pattern) (guard : d16052 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16051 p = 1 := by simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16835 p hg
    simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d501 p = 1 := by simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16839 p hg
    simpa only [d16052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16841 (p : Pattern) (guard : d16053 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16052 p = 1 := by simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16840 p hg
    simpa only [d16053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16842 (p : Pattern) (guard : d16054 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16053 p = 1 := by simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16841 p hg
    simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16843 (p : Pattern) (guard : d16055 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16054 p = 1 := by simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16842 p hg
    simpa only [d16055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16844 (p : Pattern) (guard : d16056 p = 1) : d48357 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16556 p hg
    simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16055 p = 1 := by simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16843 p hg
    simpa only [d16056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16845 (p : Pattern) (guard : d171078 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171078, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d171078, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16056 p = 1 := by simpa only [d171078, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16844 p hg
    simpa only [d171078, d48358, d171288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16846 (p : Pattern) (guard : d171079 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171079, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171078 p = 1 := by simpa only [d171079, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16845 p hg
    simpa only [d171079, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16847 (p : Pattern) (guard : d171080 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 69 with
  | false =>
    have hg : d171079 p = 1 := by simpa only [d171080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16846 p hg
    simpa only [d171080, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171080, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171080, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16848 (p : Pattern) (guard : d171081 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 51 with
  | false =>
    have hg : d171080 p = 1 := by simpa only [d171081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16847 p hg
    simpa only [d171081, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171081, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171081, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16849 (p : Pattern) (guard : d171082 p = 1) : d48358 p ≤ (0 : Int) + d171288 p := by
  cases selected : p 50 with
  | false =>
    have hg : d171081 p = 1 := by simpa only [d171082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16848 p hg
    simpa only [d171082, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171082, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16555 p hg
    simpa only [d171082, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16850 (p : Pattern) (guard : d171083 p = 1) : d48359 p ≤ (0 : Int) + d171289 p := by
  cases selected : p 49 with
  | false =>
    have hg : d171077 p = 1 := by simpa only [d171083, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16811 p hg
    simpa only [d171083, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171082 p = 1 := by simpa only [d171083, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16849 p hg
    simpa only [d171083, d48359, d171289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16851 (p : Pattern) (guard : d414 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare16852 (p : Pattern) (guard : d415 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d414 p = 1 := by simpa only [d415, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16851 p hg
    simpa only [d415, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d415, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d415, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16853 (p : Pattern) (guard : d416 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d415 p = 1 := by simpa only [d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16852 p hg
    simpa only [d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d229 p = 1 := by simpa only [d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16709 p hg
    simpa only [d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16854 (p : Pattern) (guard : d12601 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare16855 (p : Pattern) (guard : d12602 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12601 p = 1 := by simpa only [d12602, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16854 p hg
    simpa only [d12602, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12602, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d12602, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16856 (p : Pattern) (guard : d12603 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12602 p = 1 := by simpa only [d12603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16855 p hg
    simpa only [d12603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d69 p = 1 := by simpa only [d12603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16597 p hg
    simpa only [d12603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16857 (p : Pattern) (guard : d16004 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d416 p = 1 := by simpa only [d16004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16853 p hg
    simpa only [d16004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12603 p = 1 := by simpa only [d16004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16856 p hg
    simpa only [d16004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16858 (p : Pattern) (guard : d16005 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16004 p = 1 := by simpa only [d16005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16857 p hg
    simpa only [d16005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d231 p = 1 := by simpa only [d16005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16711 p hg
    simpa only [d16005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16859 (p : Pattern) (guard : d16006 p = 1) : d48362 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16006, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16594 p hg
    simpa only [d16006, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16005 p = 1 := by simpa only [d16006, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16858 p hg
    simpa only [d16006, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16860 (p : Pattern) (guard : d16007 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16007, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16593 p hg
    simpa only [d16007, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16006 p = 1 := by simpa only [d16007, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16859 p hg
    simpa only [d16007, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16861 (p : Pattern) (guard : d16008 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16007 p = 1 := by simpa only [d16008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16860 p hg
    simpa only [d16008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d234 p = 1 := by simpa only [d16008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16714 p hg
    simpa only [d16008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16862 (p : Pattern) (guard : d673 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d234 p = 1 := by simpa only [d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16714 p hg
    simpa only [d673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16863 (p : Pattern) (guard : d16175 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16008 p = 1 := by simpa only [d16175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16861 p hg
    simpa only [d16175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d673 p = 1 := by simpa only [d16175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16862 p hg
    simpa only [d16175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16864 (p : Pattern) (guard : d16176 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16175 p = 1 := by simpa only [d16176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16863 p hg
    simpa only [d16176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d16176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16865 (p : Pattern) (guard : d16177 p = 1) : d48365 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16176 p = 1 := by simpa only [d16177, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16864 p hg
    simpa only [d16177, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16177, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16608 p hg
    simpa only [d16177, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16866 (p : Pattern) (guard : d16178 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16178, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d16178, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16177 p = 1 := by simpa only [d16178, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16865 p hg
    simpa only [d16178, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16867 (p : Pattern) (guard : d682 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d673 p = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16862 p hg
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16868 (p : Pattern) (guard : d683 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d682 p = 1 := by simpa only [d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16867 p hg
    simpa only [d683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16869 (p : Pattern) (guard : d684 p = 1) : d48365 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d683 p = 1 := by simpa only [d684, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16868 p hg
    simpa only [d684, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d684, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16608 p hg
    simpa only [d684, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16870 (p : Pattern) (guard : d685 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d685, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d685, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d684 p = 1 := by simpa only [d685, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16869 p hg
    simpa only [d685, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16871 (p : Pattern) (guard : d16183 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16178 p = 1 := by simpa only [d16183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16866 p hg
    simpa only [d16183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d685 p = 1 := by simpa only [d16183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16870 p hg
    simpa only [d16183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16872 (p : Pattern) (guard : d16184 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16183 p = 1 := by simpa only [d16184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16871 p hg
    simpa only [d16184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d16184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16873 (p : Pattern) (guard : d16185 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16184 p = 1 := by simpa only [d16185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16872 p hg
    simpa only [d16185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d16185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16874 (p : Pattern) (guard : d16186 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16185 p = 1 := by simpa only [d16186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16873 p hg
    simpa only [d16186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d16186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16875 (p : Pattern) (guard : d727 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d685 p = 1 := by simpa only [d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16870 p hg
    simpa only [d727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16876 (p : Pattern) (guard : d728 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d727 p = 1 := by simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16875 p hg
    simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16877 (p : Pattern) (guard : d729 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d728 p = 1 := by simpa only [d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16876 p hg
    simpa only [d729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16878 (p : Pattern) (guard : d730 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d729 p = 1 := by simpa only [d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16877 p hg
    simpa only [d730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16879 (p : Pattern) (guard : d171084 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16186 p = 1 := by simpa only [d171084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16874 p hg
    simpa only [d171084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d730 p = 1 := by simpa only [d171084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16878 p hg
    simpa only [d171084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16880 (p : Pattern) (guard : d171085 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171084 p = 1 := by simpa only [d171085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16879 p hg
    simpa only [d171085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16881 (p : Pattern) (guard : d171086 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d171085 p = 1 := by simpa only [d171086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16880 p hg
    simpa only [d171086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16882 (p : Pattern) (guard : d171087 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171086 p = 1 := by simpa only [d171087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16881 p hg
    simpa only [d171087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16883 (p : Pattern) (guard : d171088 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171087 p = 1 := by simpa only [d171088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16882 p hg
    simpa only [d171088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16884 (p : Pattern) (guard : d171089 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171089, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d171089, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171088 p = 1 := by simpa only [d171089, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16883 p hg
    simpa only [d171089, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16885 (p : Pattern) (guard : d171090 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171089 p = 1 := by simpa only [d171090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16884 p hg
    simpa only [d171090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16886 (p : Pattern) (guard : d171091 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 69 with
  | false =>
    have hg : d171090 p = 1 := by simpa only [d171091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16885 p hg
    simpa only [d171091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16887 (p : Pattern) (guard : d171092 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 51 with
  | false =>
    have hg : d171091 p = 1 := by simpa only [d171092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16886 p hg
    simpa only [d171092, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171092, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171092, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16888 (p : Pattern) (guard : d171093 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 50 with
  | false =>
    have hg : d171092 p = 1 := by simpa only [d171093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16887 p hg
    simpa only [d171093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16889 (p : Pattern) (guard : d171094 p = 1) : d48387 p ≤ (0 : Int) + d171294 p := by
  cases selected : p 49 with
  | false =>
    have hg : d171093 p = 1 := by simpa only [d171094, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16888 p hg
    simpa only [d171094, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171094, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16625 p hg
    simpa only [d171094, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16890 (p : Pattern) (guard : d171095 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 48 with
  | false =>
    have hg : d171083 p = 1 := by simpa only [d171095, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16850 p hg
    simpa only [d171095, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171094 p = 1 := by simpa only [d171095, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16889 p hg
    simpa only [d171095, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16891 (p : Pattern) (guard : d171096 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171095 p = 1 := by simpa only [d171096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16890 p hg
    simpa only [d171096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16892 (p : Pattern) (guard : d171097 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171096 p = 1 := by simpa only [d171097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16891 p hg
    simpa only [d171097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16893 (p : Pattern) (guard : d171098 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171097 p = 1 := by simpa only [d171098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16892 p hg
    simpa only [d171098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16894 (p : Pattern) (guard : d171099 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171098 p = 1 := by simpa only [d171099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16893 p hg
    simpa only [d171099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16895 (p : Pattern) (guard : d171100 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171099 p = 1 := by simpa only [d171100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16894 p hg
    simpa only [d171100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16896 (p : Pattern) (guard : d171101 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171100 p = 1 := by simpa only [d171101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16895 p hg
    simpa only [d171101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16897 (p : Pattern) (guard : d171102 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d53677 p = 1 := by simpa only [d171102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16741 p hg
    simpa only [d171102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171101 p = 1 := by simpa only [d171102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16896 p hg
    simpa only [d171102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16898 (p : Pattern) (guard : d545 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare16899 (p : Pattern) (guard : d546 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16898 p hg
    simpa only [d546, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d546, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16900 (p : Pattern) (guard : d16073 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare16901 (p : Pattern) (guard : d16074 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16073 p = 1 := by simpa only [d16074, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16900 p hg
    simpa only [d16074, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16074, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d16074, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16902 (p : Pattern) (guard : d16075 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16899 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16074 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16901 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16903 (p : Pattern) (guard : d12748 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare16904 (p : Pattern) (guard : d12749 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12748 p = 1 := by simpa only [d12749, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16903 p hg
    simpa only [d12749, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12749, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d12749, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16905 (p : Pattern) (guard : d753 p = 1) : d47664 p ≤ (0 : Int) + d47664 p := by
  omega
theorem compare16906 (p : Pattern) (guard : d754 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16905 p hg
    simpa only [d754, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16501 p hg
    simpa only [d754, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16907 (p : Pattern) (guard : d12750 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16904 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16906 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16908 (p : Pattern) (guard : d16227 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16902 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12750 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16907 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16909 (p : Pattern) (guard : d755 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16743 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16906 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16910 (p : Pattern) (guard : d757 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16906 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16911 (p : Pattern) (guard : d758 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16909 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16910 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16912 (p : Pattern) (guard : d16228 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16908 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16911 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16913 (p : Pattern) (guard : d16229 p = 1) : d48326 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16229, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16499 p hg
    simpa only [d16229, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16228 p = 1 := by simpa only [d16229, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16912 p hg
    simpa only [d16229, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16914 (p : Pattern) (guard : d16230 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16230, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d16230, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16229 p = 1 := by simpa only [d16230, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16913 p hg
    simpa only [d16230, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16915 (p : Pattern) (guard : d762 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16910 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16503 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16916 (p : Pattern) (guard : d763 p = 1) : d48313 p ≤ (0 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16911 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16915 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16917 (p : Pattern) (guard : d764 p = 1) : d48326 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d764, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16499 p hg
    simpa only [d764, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d763 p = 1 := by simpa only [d764, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16916 p hg
    simpa only [d764, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16918 (p : Pattern) (guard : d765 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16498 p hg
    simpa only [d765, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16917 p hg
    simpa only [d765, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16919 (p : Pattern) (guard : d16231 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16230 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16914 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16918 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16920 (p : Pattern) (guard : d767 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16918 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16921 (p : Pattern) (guard : d16232 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16231 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16919 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16920 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16922 (p : Pattern) (guard : d16233 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16232 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16921 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16923 (p : Pattern) (guard : d16234 p = 1) : d48338 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16233 p = 1 := by simpa only [d16234, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16922 p hg
    simpa only [d16234, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16234, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d16234, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16924 (p : Pattern) (guard : d16235 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16235, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d16235, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16234 p = 1 := by simpa only [d16235, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16923 p hg
    simpa only [d16235, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16925 (p : Pattern) (guard : d772 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16920 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16926 (p : Pattern) (guard : d773 p = 1) : d48337 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16925 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16509 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16927 (p : Pattern) (guard : d774 p = 1) : d48338 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16926 p hg
    simpa only [d774, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d774, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16928 (p : Pattern) (guard : d775 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d775, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16927 p hg
    simpa only [d775, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16929 (p : Pattern) (guard : d16236 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16924 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16928 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16930 (p : Pattern) (guard : d16237 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16236 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16929 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16931 (p : Pattern) (guard : d16238 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16237 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16930 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16932 (p : Pattern) (guard : d16239 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16238 p = 1 := by simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16931 p hg
    simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16933 (p : Pattern) (guard : d780 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16928 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16934 (p : Pattern) (guard : d781 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16933 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16935 (p : Pattern) (guard : d782 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16934 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16936 (p : Pattern) (guard : d783 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d782 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16935 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16937 (p : Pattern) (guard : d16240 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16239 p = 1 := by simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16932 p hg
    simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d783 p = 1 := by simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16936 p hg
    simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16938 (p : Pattern) (guard : d16241 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16240 p = 1 := by simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16937 p hg
    simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16939 (p : Pattern) (guard : d16242 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16241 p = 1 := by simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16938 p hg
    simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16940 (p : Pattern) (guard : d16243 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16242 p = 1 := by simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16939 p hg
    simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16941 (p : Pattern) (guard : d16244 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16243 p = 1 := by simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16940 p hg
    simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16942 (p : Pattern) (guard : d16245 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16245, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16245, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16244 p = 1 := by simpa only [d16245, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16941 p hg
    simpa only [d16245, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16943 (p : Pattern) (guard : d16230 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16230, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16527 p hg
    simpa only [d16230, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16229 p = 1 := by simpa only [d16230, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16913 p hg
    simpa only [d16230, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16944 (p : Pattern) (guard : d765 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16527 p hg
    simpa only [d765, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16917 p hg
    simpa only [d765, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16945 (p : Pattern) (guard : d16231 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16230 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16943 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16944 p hg
    simpa only [d16231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16946 (p : Pattern) (guard : d767 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16944 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16947 (p : Pattern) (guard : d16232 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16231 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16945 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16946 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16948 (p : Pattern) (guard : d16233 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16232 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16947 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d16233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16949 (p : Pattern) (guard : d16234 p = 1) : d48329 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d16233 p = 1 := by simpa only [d16234, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16948 p hg
    simpa only [d16234, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16234, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d16234, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16950 (p : Pattern) (guard : d16235 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16235, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16526 p hg
    simpa only [d16235, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16234 p = 1 := by simpa only [d16235, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16949 p hg
    simpa only [d16235, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16951 (p : Pattern) (guard : d772 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16946 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16952 (p : Pattern) (guard : d773 p = 1) : d48327 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16951 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16529 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16953 (p : Pattern) (guard : d774 p = 1) : d48329 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16952 p hg
    simpa only [d774, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16513 p hg
    simpa only [d774, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16954 (p : Pattern) (guard : d775 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16526 p hg
    simpa only [d775, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16953 p hg
    simpa only [d775, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16955 (p : Pattern) (guard : d16236 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d16235 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16950 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16954 p hg
    simpa only [d16236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16956 (p : Pattern) (guard : d16237 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d16236 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16955 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16957 (p : Pattern) (guard : d16238 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d16237 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16956 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16958 (p : Pattern) (guard : d16239 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16238 p = 1 := by simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16957 p hg
    simpa only [d16239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16959 (p : Pattern) (guard : d780 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16954 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16960 (p : Pattern) (guard : d781 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16959 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16961 (p : Pattern) (guard : d782 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16960 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16962 (p : Pattern) (guard : d783 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d782 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16961 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16963 (p : Pattern) (guard : d16240 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16239 p = 1 := by simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16958 p hg
    simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d783 p = 1 := by simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16962 p hg
    simpa only [d16240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16964 (p : Pattern) (guard : d16241 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16240 p = 1 := by simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16963 p hg
    simpa only [d16241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16965 (p : Pattern) (guard : d16242 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16241 p = 1 := by simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16964 p hg
    simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16966 (p : Pattern) (guard : d16243 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16242 p = 1 := by simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16965 p hg
    simpa only [d16243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16967 (p : Pattern) (guard : d16244 p = 1) : d48330 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16243 p = 1 := by simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16966 p hg
    simpa only [d16244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16968 (p : Pattern) (guard : d16248 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d16238 p = 1 := by simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16931 p hg
    simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16969 (p : Pattern) (guard : d793 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d782 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16935 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16970 (p : Pattern) (guard : d16249 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d16248 p = 1 := by simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16968 p hg
    simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16969 p hg
    simpa only [d16249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16971 (p : Pattern) (guard : d16250 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16249 p = 1 := by simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16970 p hg
    simpa only [d16250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16972 (p : Pattern) (guard : d16251 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d16250 p = 1 := by simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16971 p hg
    simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16973 (p : Pattern) (guard : d16252 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16251 p = 1 := by simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16972 p hg
    simpa only [d16252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16974 (p : Pattern) (guard : d16253 p = 1) : d48339 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16496 p hg
    simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16252 p = 1 := by simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16973 p hg
    simpa only [d16253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16975 (p : Pattern) (guard : d16254 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d16244 p = 1 := by simpa only [d16254, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16967 p hg
    simpa only [d16254, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16253 p = 1 := by simpa only [d16254, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16974 p hg
    simpa only [d16254, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16976 (p : Pattern) (guard : d16255 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d16245 p = 1 := by simpa only [d16255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16942 p hg
    simpa only [d16255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16254 p = 1 := by simpa only [d16255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16975 p hg
    simpa only [d16255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16977 (p : Pattern) (guard : d16256 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d16255 p = 1 := by simpa only [d16256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16976 p hg
    simpa only [d16256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d16256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16978 (p : Pattern) (guard : d171103 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d16256 p = 1 := by simpa only [d171103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16977 p hg
    simpa only [d171103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d171103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16979 (p : Pattern) (guard : d171104 p = 1) : d48340 p ≤ (0 : Int) + d48142 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16494 p hg
    simpa only [d171104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171103 p = 1 := by simpa only [d171104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16978 p hg
    simpa only [d171104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16980 (p : Pattern) (guard : d545 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare16981 (p : Pattern) (guard : d546 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16980 p hg
    simpa only [d546, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d546, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16982 (p : Pattern) (guard : d16073 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare16983 (p : Pattern) (guard : d16074 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16073 p = 1 := by simpa only [d16074, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16982 p hg
    simpa only [d16074, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16074, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d16074, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16984 (p : Pattern) (guard : d16075 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16981 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16074 p = 1 := by simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16983 p hg
    simpa only [d16075, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16985 (p : Pattern) (guard : d12748 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare16986 (p : Pattern) (guard : d12749 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d12748 p = 1 := by simpa only [d12749, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16985 p hg
    simpa only [d12749, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d12749, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d12749, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16987 (p : Pattern) (guard : d753 p = 1) : d47737 p ≤ (0 : Int) + d47737 p := by
  omega
theorem compare16988 (p : Pattern) (guard : d754 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16987 p hg
    simpa only [d754, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16561 p hg
    simpa only [d754, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16989 (p : Pattern) (guard : d12750 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16986 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16988 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16990 (p : Pattern) (guard : d16227 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16984 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12750 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16989 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16991 (p : Pattern) (guard : d755 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16813 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16988 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16992 (p : Pattern) (guard : d757 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16988 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16993 (p : Pattern) (guard : d758 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16991 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16992 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16994 (p : Pattern) (guard : d16228 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16990 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16993 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16995 (p : Pattern) (guard : d16229 p = 1) : d48346 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16229, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16559 p hg
    simpa only [d16229, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16228 p = 1 := by simpa only [d16229, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16994 p hg
    simpa only [d16229, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16996 (p : Pattern) (guard : d16230 p = 1) : d48354 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16230, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16558 p hg
    simpa only [d16230, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16229 p = 1 := by simpa only [d16230, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16995 p hg
    simpa only [d16230, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16997 (p : Pattern) (guard : d762 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16992 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16563 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16998 (p : Pattern) (guard : d763 p = 1) : d48345 p ≤ (0 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16993 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16997 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare16999 (p : Pattern) (guard : d764 p = 1) : d48346 p ≤ (0 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d764, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16559 p hg
    simpa only [d764, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d763 p = 1 := by simpa only [d764, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16998 p hg
    simpa only [d764, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
