import NetHack.Soko22Hazard87.Compare145
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare36500 (p : Pattern) (guard : d316591 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316590 p = 1 := by simpa only [d316591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d316591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316581 p = 1 := by simpa only [d316591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36478 p hg
    simpa only [d316591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36501 (p : Pattern) (guard : d316683 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d316683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316591 p = 1 := by simpa only [d316683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36500 p hg
    simpa only [d316683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36502 (p : Pattern) (guard : d316592 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316591 p = 1 := by simpa only [d316592, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36196 p hg
    simpa only [d316592, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316592, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d316592, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36503 (p : Pattern) (guard : d316684 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316683 p = 1 := by simpa only [d316684, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36501 p hg
    simpa only [d316684, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316592 p = 1 := by simpa only [d316684, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36502 p hg
    simpa only [d316684, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36504 (p : Pattern) (guard : d316588 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316578 p = 1 := by simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36487 p hg
    simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36505 (p : Pattern) (guard : d316589 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316588 p = 1 := by simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36504 p hg
    simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36506 (p : Pattern) (guard : d316590 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316589 p = 1 := by simpa only [d316590, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36505 p hg
    simpa only [d316590, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316590, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d316590, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36507 (p : Pattern) (guard : d316591 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316590 p = 1 := by simpa only [d316591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36506 p hg
    simpa only [d316591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316581 p = 1 := by simpa only [d316591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36490 p hg
    simpa only [d316591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36508 (p : Pattern) (guard : d316592 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316591 p = 1 := by simpa only [d316592, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36507 p hg
    simpa only [d316592, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316592, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316592, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36509 (p : Pattern) (guard : d316593 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316592 p = 1 := by simpa only [d316593, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36508 p hg
    simpa only [d316593, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316593, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d316593, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36510 (p : Pattern) (guard : d316685 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d316684 p = 1 := by simpa only [d316685, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36503 p hg
    simpa only [d316685, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316593 p = 1 := by simpa only [d316685, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36509 p hg
    simpa only [d316685, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36511 (p : Pattern) (guard : d316686 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316685 p = 1 := by simpa only [d316686, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36510 p hg
    simpa only [d316686, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316686, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d316686, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36512 (p : Pattern) (guard : d316687 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316686 p = 1 := by simpa only [d316687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36511 p hg
    simpa only [d316687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316455 p = 1 := by simpa only [d316687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35970 p hg
    simpa only [d316687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36513 (p : Pattern) (guard : d316688 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d316682 p = 1 := by simpa only [d316688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36496 p hg
    simpa only [d316688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316687 p = 1 := by simpa only [d316688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36512 p hg
    simpa only [d316688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36514 (p : Pattern) (guard : d40149 p = 1) : d47630 p ≤ (3 : Int) + d47630 p := by
  omega
theorem compare36515 (p : Pattern) (guard : d317407 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d40149 p = 1 := by simpa only [d317407, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36514 p hg
    simpa only [d317407, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317407, d50139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35005 p hg
    simpa only [d317407, d50139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36516 (p : Pattern) (guard : d317408 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317407 p = 1 := by simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36515 p hg
    simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36517 (p : Pattern) (guard : d317409 p = 1) : d50139 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d317408 p = 1 := by simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36516 p hg
    simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35003 p hg
    simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36518 (p : Pattern) (guard : d317410 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d317409 p = 1 := by simpa only [d317410, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36517 p hg
    simpa only [d317410, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317410, d50168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35009 p hg
    simpa only [d317410, d50168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36519 (p : Pattern) (guard : d317411 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35493 p hg
    simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317410 p = 1 := by simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36518 p hg
    simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36520 (p : Pattern) (guard : d317412 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317411 p = 1 := by simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36519 p hg
    simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316231 p = 1 := by simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35500 p hg
    simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36521 (p : Pattern) (guard : d317413 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317412 p = 1 := by simpa only [d317413, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36520 p hg
    simpa only [d317413, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317413, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d317413, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36522 (p : Pattern) (guard : d317414 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316356 p = 1 := by simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35911 p hg
    simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317413 p = 1 := by simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36521 p hg
    simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36523 (p : Pattern) (guard : d317589 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317414 p = 1 := by simpa only [d317589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36522 p hg
    simpa only [d317589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36524 (p : Pattern) (guard : d317415 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317414 p = 1 := by simpa only [d317415, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36047 p hg
    simpa only [d317415, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317415, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317415, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36525 (p : Pattern) (guard : d317590 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317589 p = 1 := by simpa only [d317590, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36523 p hg
    simpa only [d317590, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317415 p = 1 := by simpa only [d317590, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36524 p hg
    simpa only [d317590, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36526 (p : Pattern) (guard : d40149 p = 1) : d47634 p ≤ (3 : Int) + d47634 p := by
  omega
theorem compare36527 (p : Pattern) (guard : d317407 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d40149 p = 1 := by simpa only [d317407, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36526 p hg
    simpa only [d317407, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317407, d50144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35022 p hg
    simpa only [d317407, d50144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36528 (p : Pattern) (guard : d317408 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317407 p = 1 := by simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36527 p hg
    simpa only [d317408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36529 (p : Pattern) (guard : d317409 p = 1) : d50144 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d317408 p = 1 := by simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36528 p hg
    simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d317409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36530 (p : Pattern) (guard : d317410 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d317409 p = 1 := by simpa only [d317410, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36529 p hg
    simpa only [d317410, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317410, d50211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35026 p hg
    simpa only [d317410, d50211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36531 (p : Pattern) (guard : d317411 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35511 p hg
    simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317410 p = 1 := by simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36530 p hg
    simpa only [d317411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36532 (p : Pattern) (guard : d317412 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317411 p = 1 := by simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36531 p hg
    simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316231 p = 1 := by simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35518 p hg
    simpa only [d317412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36533 (p : Pattern) (guard : d317413 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317412 p = 1 := by simpa only [d317413, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36532 p hg
    simpa only [d317413, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317413, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d317413, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36534 (p : Pattern) (guard : d317414 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316356 p = 1 := by simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35924 p hg
    simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317413 p = 1 := by simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36533 p hg
    simpa only [d317414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36535 (p : Pattern) (guard : d317415 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317414 p = 1 := by simpa only [d317415, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36534 p hg
    simpa only [d317415, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317415, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317415, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36536 (p : Pattern) (guard : d317416 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317415 p = 1 := by simpa only [d317416, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36535 p hg
    simpa only [d317416, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317416, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317416, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36537 (p : Pattern) (guard : d317591 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317590 p = 1 := by simpa only [d317591, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36525 p hg
    simpa only [d317591, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317416 p = 1 := by simpa only [d317591, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36536 p hg
    simpa only [d317591, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36538 (p : Pattern) (guard : d317592 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317591 p = 1 := by simpa only [d317592, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36537 p hg
    simpa only [d317592, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317592, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d317592, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36539 (p : Pattern) (guard : d317419 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317413 p = 1 := by simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36521 p hg
    simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35937 p hg
    simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36540 (p : Pattern) (guard : d317593 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317419 p = 1 := by simpa only [d317593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36539 p hg
    simpa only [d317593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36541 (p : Pattern) (guard : d317420 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317419 p = 1 := by simpa only [d317420, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36052 p hg
    simpa only [d317420, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317420, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317420, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36542 (p : Pattern) (guard : d317594 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317593 p = 1 := by simpa only [d317594, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36540 p hg
    simpa only [d317594, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317420 p = 1 := by simpa only [d317594, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36541 p hg
    simpa only [d317594, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36543 (p : Pattern) (guard : d317419 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317413 p = 1 := by simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36533 p hg
    simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35949 p hg
    simpa only [d317419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36544 (p : Pattern) (guard : d317420 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317419 p = 1 := by simpa only [d317420, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36543 p hg
    simpa only [d317420, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317420, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317420, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36545 (p : Pattern) (guard : d317421 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317420 p = 1 := by simpa only [d317421, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36544 p hg
    simpa only [d317421, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317421, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317421, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36546 (p : Pattern) (guard : d317595 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317594 p = 1 := by simpa only [d317595, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36542 p hg
    simpa only [d317595, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317421 p = 1 := by simpa only [d317595, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36545 p hg
    simpa only [d317595, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36547 (p : Pattern) (guard : d317596 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317595 p = 1 := by simpa only [d317596, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36546 p hg
    simpa only [d317596, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317596, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d317596, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36548 (p : Pattern) (guard : d317597 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317592 p = 1 := by simpa only [d317597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36538 p hg
    simpa only [d317597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317596 p = 1 := by simpa only [d317597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36547 p hg
    simpa only [d317597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36549 (p : Pattern) (guard : d317425 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317410 p = 1 := by simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36518 p hg
    simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35010 p hg
    simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36550 (p : Pattern) (guard : d317426 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317425 p = 1 := by simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36549 p hg
    simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35012 p hg
    simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36551 (p : Pattern) (guard : d317427 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317426 p = 1 := by simpa only [d317427, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36550 p hg
    simpa only [d317427, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317427, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d317427, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36552 (p : Pattern) (guard : d317428 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317427 p = 1 := by simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36551 p hg
    simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36553 (p : Pattern) (guard : d317598 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317428 p = 1 := by simpa only [d317598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36552 p hg
    simpa only [d317598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36554 (p : Pattern) (guard : d317429 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317428 p = 1 := by simpa only [d317429, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36061 p hg
    simpa only [d317429, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317429, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317429, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36555 (p : Pattern) (guard : d317599 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317598 p = 1 := by simpa only [d317599, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36553 p hg
    simpa only [d317599, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317429 p = 1 := by simpa only [d317599, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36554 p hg
    simpa only [d317599, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36556 (p : Pattern) (guard : d317425 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317410 p = 1 := by simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36530 p hg
    simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35027 p hg
    simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36557 (p : Pattern) (guard : d317426 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317425 p = 1 := by simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36556 p hg
    simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35029 p hg
    simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36558 (p : Pattern) (guard : d317427 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317426 p = 1 := by simpa only [d317427, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36557 p hg
    simpa only [d317427, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317427, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d317427, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36559 (p : Pattern) (guard : d317428 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317427 p = 1 := by simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36558 p hg
    simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35033 p hg
    simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36560 (p : Pattern) (guard : d317429 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317428 p = 1 := by simpa only [d317429, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36559 p hg
    simpa only [d317429, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317429, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317429, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36561 (p : Pattern) (guard : d317430 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317429 p = 1 := by simpa only [d317430, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36560 p hg
    simpa only [d317430, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317430, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317430, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36562 (p : Pattern) (guard : d317600 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317599 p = 1 := by simpa only [d317600, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36555 p hg
    simpa only [d317600, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317430 p = 1 := by simpa only [d317600, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36561 p hg
    simpa only [d317600, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36563 (p : Pattern) (guard : d317601 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317600 p = 1 := by simpa only [d317601, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36562 p hg
    simpa only [d317601, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317601, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d317601, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36564 (p : Pattern) (guard : d317602 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316455 p = 1 := by simpa only [d317602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35970 p hg
    simpa only [d317602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317601 p = 1 := by simpa only [d317602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36563 p hg
    simpa only [d317602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36565 (p : Pattern) (guard : d317603 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317597 p = 1 := by simpa only [d317603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36548 p hg
    simpa only [d317603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317602 p = 1 := by simpa only [d317603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36564 p hg
    simpa only [d317603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36566 (p : Pattern) (guard : d317604 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d316688 p = 1 := by simpa only [d317604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36513 p hg
    simpa only [d317604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317603 p = 1 := by simpa only [d317604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36565 p hg
    simpa only [d317604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36567 (p : Pattern) (guard : d317605 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317605, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d317605, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317604 p = 1 := by simpa only [d317605, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36566 p hg
    simpa only [d317605, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36568 (p : Pattern) (guard : d317606 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317606, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d317606, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317605 p = 1 := by simpa only [d317606, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36567 p hg
    simpa only [d317606, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36569 (p : Pattern) (guard : d317607 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317601 p = 1 := by simpa only [d317607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36563 p hg
    simpa only [d317607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d317607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36570 (p : Pattern) (guard : d317608 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317602 p = 1 := by simpa only [d317608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36564 p hg
    simpa only [d317608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317607 p = 1 := by simpa only [d317608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36569 p hg
    simpa only [d317608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36571 (p : Pattern) (guard : d317609 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317603 p = 1 := by simpa only [d317609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36565 p hg
    simpa only [d317609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317608 p = 1 := by simpa only [d317609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36570 p hg
    simpa only [d317609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36572 (p : Pattern) (guard : d317610 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317610, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d317610, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317609 p = 1 := by simpa only [d317610, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36571 p hg
    simpa only [d317610, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36573 (p : Pattern) (guard : d317611 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317611, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d317611, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317610 p = 1 := by simpa only [d317611, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36572 p hg
    simpa only [d317611, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36574 (p : Pattern) (guard : d317612 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317606 p = 1 := by simpa only [d317612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36568 p hg
    simpa only [d317612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317611 p = 1 := by simpa only [d317612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36573 p hg
    simpa only [d317612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36575 (p : Pattern) (guard : d317435 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317410 p = 1 := by simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36518 p hg
    simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35011 p hg
    simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36576 (p : Pattern) (guard : d317436 p = 1) : d50168 p ≤ (3 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317435 p = 1 := by simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36575 p hg
    simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35012 p hg
    simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36577 (p : Pattern) (guard : d317437 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317436 p = 1 := by simpa only [d317437, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36576 p hg
    simpa only [d317437, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317437, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35014 p hg
    simpa only [d317437, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36578 (p : Pattern) (guard : d317438 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317413 p = 1 := by simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36521 p hg
    simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317437 p = 1 := by simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36577 p hg
    simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36579 (p : Pattern) (guard : d317613 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317438 p = 1 := by simpa only [d317613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36578 p hg
    simpa only [d317613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36580 (p : Pattern) (guard : d317439 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317438 p = 1 := by simpa only [d317439, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36071 p hg
    simpa only [d317439, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317439, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317439, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36581 (p : Pattern) (guard : d317614 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317613 p = 1 := by simpa only [d317614, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36579 p hg
    simpa only [d317614, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317439 p = 1 := by simpa only [d317614, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36580 p hg
    simpa only [d317614, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36582 (p : Pattern) (guard : d317435 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317410 p = 1 := by simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36530 p hg
    simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35028 p hg
    simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36583 (p : Pattern) (guard : d317436 p = 1) : d50211 p ≤ (3 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317435 p = 1 := by simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36582 p hg
    simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35029 p hg
    simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36584 (p : Pattern) (guard : d317437 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317436 p = 1 := by simpa only [d317437, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36583 p hg
    simpa only [d317437, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317437, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d317437, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36585 (p : Pattern) (guard : d317438 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317413 p = 1 := by simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36533 p hg
    simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317437 p = 1 := by simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36584 p hg
    simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36586 (p : Pattern) (guard : d317439 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317438 p = 1 := by simpa only [d317439, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36585 p hg
    simpa only [d317439, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317439, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317439, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36587 (p : Pattern) (guard : d317440 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317439 p = 1 := by simpa only [d317440, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36586 p hg
    simpa only [d317440, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317440, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317440, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36588 (p : Pattern) (guard : d317615 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317614 p = 1 := by simpa only [d317615, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36581 p hg
    simpa only [d317615, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317440 p = 1 := by simpa only [d317615, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36587 p hg
    simpa only [d317615, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36589 (p : Pattern) (guard : d317616 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317615 p = 1 := by simpa only [d317616, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36588 p hg
    simpa only [d317616, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317616, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d317616, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36590 (p : Pattern) (guard : d317443 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317437 p = 1 := by simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36577 p hg
    simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36591 (p : Pattern) (guard : d317617 p = 1) : d50210 p ≤ (3 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35002 p hg
    simpa only [d317617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317443 p = 1 := by simpa only [d317617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36590 p hg
    simpa only [d317617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36592 (p : Pattern) (guard : d317444 p = 1) : d50420 p ≤ (3 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317443 p = 1 := by simpa only [d317444, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36076 p hg
    simpa only [d317444, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317444, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d317444, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36593 (p : Pattern) (guard : d317618 p = 1) : d50421 p ≤ (3 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317617 p = 1 := by simpa only [d317618, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36591 p hg
    simpa only [d317618, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317444 p = 1 := by simpa only [d317618, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36592 p hg
    simpa only [d317618, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36594 (p : Pattern) (guard : d317443 p = 1) : d50212 p ≤ (3 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317437 p = 1 := by simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36584 p hg
    simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35033 p hg
    simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36595 (p : Pattern) (guard : d317444 p = 1) : d50223 p ≤ (3 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317443 p = 1 := by simpa only [d317444, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36594 p hg
    simpa only [d317444, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317444, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317444, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36596 (p : Pattern) (guard : d317445 p = 1) : d50224 p ≤ (3 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317444 p = 1 := by simpa only [d317445, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36595 p hg
    simpa only [d317445, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317445, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d317445, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36597 (p : Pattern) (guard : d317619 p = 1) : d50422 p ≤ (3 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317618 p = 1 := by simpa only [d317619, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36593 p hg
    simpa only [d317619, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317445 p = 1 := by simpa only [d317619, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36596 p hg
    simpa only [d317619, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36598 (p : Pattern) (guard : d317620 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317619 p = 1 := by simpa only [d317620, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36597 p hg
    simpa only [d317620, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317620, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35038 p hg
    simpa only [d317620, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36599 (p : Pattern) (guard : d317621 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317616 p = 1 := by simpa only [d317621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36589 p hg
    simpa only [d317621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317620 p = 1 := by simpa only [d317621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36598 p hg
    simpa only [d317621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36600 (p : Pattern) (guard : d317622 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317621 p = 1 := by simpa only [d317622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36599 p hg
    simpa only [d317622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317607 p = 1 := by simpa only [d317622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36569 p hg
    simpa only [d317622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36601 (p : Pattern) (guard : d317623 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317603 p = 1 := by simpa only [d317623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36565 p hg
    simpa only [d317623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317622 p = 1 := by simpa only [d317623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36600 p hg
    simpa only [d317623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36602 (p : Pattern) (guard : d317624 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317624, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d317624, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317623 p = 1 := by simpa only [d317624, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36601 p hg
    simpa only [d317624, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36603 (p : Pattern) (guard : d317625 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317625, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d317625, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317624 p = 1 := by simpa only [d317625, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36602 p hg
    simpa only [d317625, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36604 (p : Pattern) (guard : d317626 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317620 p = 1 := by simpa only [d317626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36598 p hg
    simpa only [d317626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d317626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36605 (p : Pattern) (guard : d317627 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317626 p = 1 := by simpa only [d317627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36604 p hg
    simpa only [d317627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d317627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36606 (p : Pattern) (guard : d317628 p = 1) : d50426 p ≤ (3 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317622 p = 1 := by simpa only [d317628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36600 p hg
    simpa only [d317628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317627 p = 1 := by simpa only [d317628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36605 p hg
    simpa only [d317628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36607 (p : Pattern) (guard : d317629 p = 1) : d50427 p ≤ (3 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317629, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35001 p hg
    simpa only [d317629, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317628 p = 1 := by simpa only [d317629, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36606 p hg
    simpa only [d317629, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36608 (p : Pattern) (guard : d317630 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317630, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d317630, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317629 p = 1 := by simpa only [d317630, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36607 p hg
    simpa only [d317630, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36609 (p : Pattern) (guard : d317631 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317625 p = 1 := by simpa only [d317631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36603 p hg
    simpa only [d317631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317630 p = 1 := by simpa only [d317631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36608 p hg
    simpa only [d317631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36610 (p : Pattern) (guard : d317632 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317612 p = 1 := by simpa only [d317632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36574 p hg
    simpa only [d317632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317631 p = 1 := by simpa only [d317632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36609 p hg
    simpa only [d317632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36611 (p : Pattern) (guard : d317633 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317632 p = 1 := by simpa only [d317633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36610 p hg
    simpa only [d317633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d317633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36612 (p : Pattern) (guard : d317634 p = 1) : d50430 p ≤ (3 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317633 p = 1 := by simpa only [d317634, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36611 p hg
    simpa only [d317634, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317634, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d317634, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36613 (p : Pattern) (guard : d317635 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317635, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d317635, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317634 p = 1 := by simpa only [d317635, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36612 p hg
    simpa only [d317635, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36614 (p : Pattern) (guard : d317636 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317630 p = 1 := by simpa only [d317636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36608 p hg
    simpa only [d317636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d317636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36615 (p : Pattern) (guard : d317637 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317631 p = 1 := by simpa only [d317637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36609 p hg
    simpa only [d317637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317636 p = 1 := by simpa only [d317637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36614 p hg
    simpa only [d317637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36616 (p : Pattern) (guard : d317638 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317637 p = 1 := by simpa only [d317638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36615 p hg
    simpa only [d317638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d317638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36617 (p : Pattern) (guard : d317639 p = 1) : d50430 p ≤ (3 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317638 p = 1 := by simpa only [d317639, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36616 p hg
    simpa only [d317639, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317639, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d317639, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36618 (p : Pattern) (guard : d317640 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317640, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d317640, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317639 p = 1 := by simpa only [d317640, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36617 p hg
    simpa only [d317640, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36619 (p : Pattern) (guard : d317641 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317635 p = 1 := by simpa only [d317641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36613 p hg
    simpa only [d317641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317640 p = 1 := by simpa only [d317641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36618 p hg
    simpa only [d317641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36620 (p : Pattern) (guard : d317642 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317641 p = 1 := by simpa only [d317642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36619 p hg
    simpa only [d317642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36621 (p : Pattern) (guard : d317643 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317642 p = 1 := by simpa only [d317643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36620 p hg
    simpa only [d317643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36622 (p : Pattern) (guard : d317644 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317643 p = 1 := by simpa only [d317644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36621 p hg
    simpa only [d317644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36623 (p : Pattern) (guard : d317645 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317636 p = 1 := by simpa only [d317645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36614 p hg
    simpa only [d317645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d317645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36624 (p : Pattern) (guard : d317646 p = 1) : d50428 p ≤ (3 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317645 p = 1 := by simpa only [d317646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36623 p hg
    simpa only [d317646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d317646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36625 (p : Pattern) (guard : d317647 p = 1) : d50430 p ≤ (3 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317646 p = 1 := by simpa only [d317647, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36624 p hg
    simpa only [d317647, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317647, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35050 p hg
    simpa only [d317647, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36626 (p : Pattern) (guard : d317648 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317648, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d317648, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317647 p = 1 := by simpa only [d317648, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36625 p hg
    simpa only [d317648, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36627 (p : Pattern) (guard : d317649 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317640 p = 1 := by simpa only [d317649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36618 p hg
    simpa only [d317649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317648 p = 1 := by simpa only [d317649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36626 p hg
    simpa only [d317649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36628 (p : Pattern) (guard : d317650 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317649 p = 1 := by simpa only [d317650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36627 p hg
    simpa only [d317650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36629 (p : Pattern) (guard : d317651 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317650 p = 1 := by simpa only [d317651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36628 p hg
    simpa only [d317651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36630 (p : Pattern) (guard : d317652 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317651 p = 1 := by simpa only [d317652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36629 p hg
    simpa only [d317652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36631 (p : Pattern) (guard : d317653 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317644 p = 1 := by simpa only [d317653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36622 p hg
    simpa only [d317653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317652 p = 1 := by simpa only [d317653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36630 p hg
    simpa only [d317653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36632 (p : Pattern) (guard : d317654 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317653 p = 1 := by simpa only [d317654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36631 p hg
    simpa only [d317654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36633 (p : Pattern) (guard : d317655 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317640 p = 1 := by simpa only [d317655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36618 p hg
    simpa only [d317655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36634 (p : Pattern) (guard : d317656 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317655 p = 1 := by simpa only [d317656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36633 p hg
    simpa only [d317656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36635 (p : Pattern) (guard : d317657 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317656 p = 1 := by simpa only [d317657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36634 p hg
    simpa only [d317657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36636 (p : Pattern) (guard : d317658 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317657 p = 1 := by simpa only [d317658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36635 p hg
    simpa only [d317658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36637 (p : Pattern) (guard : d317659 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317658 p = 1 := by simpa only [d317659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36636 p hg
    simpa only [d317659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36638 (p : Pattern) (guard : d317660 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d317659 p = 1 := by simpa only [d317660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36637 p hg
    simpa only [d317660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36639 (p : Pattern) (guard : d317661 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317654 p = 1 := by simpa only [d317661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36632 p hg
    simpa only [d317661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317660 p = 1 := by simpa only [d317661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36638 p hg
    simpa only [d317661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36640 (p : Pattern) (guard : d317662 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317661 p = 1 := by simpa only [d317662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36639 p hg
    simpa only [d317662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36641 (p : Pattern) (guard : d317663 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317662 p = 1 := by simpa only [d317663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36640 p hg
    simpa only [d317663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36642 (p : Pattern) (guard : d317664 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317664, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317664, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317663 p = 1 := by simpa only [d317664, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36641 p hg
    simpa only [d317664, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36643 (p : Pattern) (guard : d317665 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d317665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317664 p = 1 := by simpa only [d317665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36642 p hg
    simpa only [d317665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36644 (p : Pattern) (guard : d317666 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317648 p = 1 := by simpa only [d317666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36626 p hg
    simpa only [d317666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36645 (p : Pattern) (guard : d317667 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317666 p = 1 := by simpa only [d317667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36644 p hg
    simpa only [d317667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36646 (p : Pattern) (guard : d317668 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317667 p = 1 := by simpa only [d317668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36645 p hg
    simpa only [d317668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36647 (p : Pattern) (guard : d317669 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317668 p = 1 := by simpa only [d317669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36646 p hg
    simpa only [d317669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36648 (p : Pattern) (guard : d317670 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317669 p = 1 := by simpa only [d317670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d317670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36649 (p : Pattern) (guard : d317671 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317670 p = 1 := by simpa only [d317671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36648 p hg
    simpa only [d317671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36650 (p : Pattern) (guard : d317672 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317671 p = 1 := by simpa only [d317672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36649 p hg
    simpa only [d317672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36651 (p : Pattern) (guard : d317673 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317672 p = 1 := by simpa only [d317673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36650 p hg
    simpa only [d317673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36652 (p : Pattern) (guard : d317674 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34999 p hg
    simpa only [d317674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317673 p = 1 := by simpa only [d317674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36651 p hg
    simpa only [d317674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36653 (p : Pattern) (guard : d317675 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317675, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d317675, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317674 p = 1 := by simpa only [d317675, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36652 p hg
    simpa only [d317675, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36654 (p : Pattern) (guard : d317676 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d317676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317675 p = 1 := by simpa only [d317676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36653 p hg
    simpa only [d317676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36655 (p : Pattern) (guard : d317677 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d317665 p = 1 := by simpa only [d317677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36643 p hg
    simpa only [d317677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317676 p = 1 := by simpa only [d317677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36654 p hg
    simpa only [d317677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36656 (p : Pattern) (guard : d317678 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d317677 p = 1 := by simpa only [d317678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36655 p hg
    simpa only [d317678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d317678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36657 (p : Pattern) (guard : d317679 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d317678 p = 1 := by simpa only [d317679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36656 p hg
    simpa only [d317679, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317679, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34998 p hg
    simpa only [d317679, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36658 (p : Pattern) (guard : d317680 p = 1) : d50492 p ≤ (3 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d317679 p = 1 := by simpa only [d317680, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36657 p hg
    simpa only [d317680, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317680, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35067 p hg
    simpa only [d317680, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36659 (p : Pattern) (guard : d317681 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d317588 p = 1 := by simpa only [d317681, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36455 p hg
    simpa only [d317681, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317680 p = 1 := by simpa only [d317681, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36658 p hg
    simpa only [d317681, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36660 (p : Pattern) (guard : d317682 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317681 p = 1 := by simpa only [d317682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36659 p hg
    simpa only [d317682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36661 (p : Pattern) (guard : d317683 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317682 p = 1 := by simpa only [d317683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36660 p hg
    simpa only [d317683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36662 (p : Pattern) (guard : d317684 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317683 p = 1 := by simpa only [d317684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36661 p hg
    simpa only [d317684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36663 (p : Pattern) (guard : d317685 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317684 p = 1 := by simpa only [d317685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36662 p hg
    simpa only [d317685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36664 (p : Pattern) (guard : d317686 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317685 p = 1 := by simpa only [d317686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36663 p hg
    simpa only [d317686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36665 (p : Pattern) (guard : d317687 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317686 p = 1 := by simpa only [d317687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36664 p hg
    simpa only [d317687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36666 (p : Pattern) (guard : d317688 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317687 p = 1 := by simpa only [d317688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36665 p hg
    simpa only [d317688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36667 (p : Pattern) (guard : d317689 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34860 p hg
    simpa only [d317689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317688 p = 1 := by simpa only [d317689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36666 p hg
    simpa only [d317689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36668 (p : Pattern) (guard : d317690 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d316506 p = 1 := by simpa only [d317690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36038 p hg
    simpa only [d317690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317689 p = 1 := by simpa only [d317690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36667 p hg
    simpa only [d317690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36669 (p : Pattern) (guard : d40834 p = 1) : d47617 p ≤ (3 : Int) + d47617 p := by
  omega
theorem compare36670 (p : Pattern) (guard : d317691 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d40834 p = 1 := by simpa only [d317691, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36669 p hg
    simpa only [d317691, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317691, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34870 p hg
    simpa only [d317691, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36671 (p : Pattern) (guard : d317692 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317691 p = 1 := by simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36670 p hg
    simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36672 (p : Pattern) (guard : d317693 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d317692 p = 1 := by simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36671 p hg
    simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36673 (p : Pattern) (guard : d317694 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d317693 p = 1 := by simpa only [d317694, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36672 p hg
    simpa only [d317694, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317694, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34874 p hg
    simpa only [d317694, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36674 (p : Pattern) (guard : d317695 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317694 p = 1 := by simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36673 p hg
    simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36675 (p : Pattern) (guard : d1531 p = 1) : d47617 p ≤ (3 : Int) + d47617 p := by
  omega
theorem compare36676 (p : Pattern) (guard : d1547 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36675 p hg
    simpa only [d1547, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34870 p hg
    simpa only [d1547, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36677 (p : Pattern) (guard : d39244 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36676 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36678 (p : Pattern) (guard : d258107 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d39244 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36677 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36679 (p : Pattern) (guard : d258108 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258107 p = 1 := by simpa only [d258108, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36678 p hg
    simpa only [d258108, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258108, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34874 p hg
    simpa only [d258108, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36680 (p : Pattern) (guard : d316767 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34354 p = 1 := by simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35665 p hg
    simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36679 p hg
    simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36681 (p : Pattern) (guard : d317696 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317695 p = 1 := by simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36674 p hg
    simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316767 p = 1 := by simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36680 p hg
    simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36682 (p : Pattern) (guard : d317697 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317696 p = 1 := by simpa only [d317697, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36681 p hg
    simpa only [d317697, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317697, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d317697, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36683 (p : Pattern) (guard : d317698 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d34357 p = 1 := by simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36173 p hg
    simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317697 p = 1 := by simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36682 p hg
    simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36684 (p : Pattern) (guard : d317699 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317698 p = 1 := by simpa only [d317699, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36683 p hg
    simpa only [d317699, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317699, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d317699, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36685 (p : Pattern) (guard : d317700 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317699 p = 1 := by simpa only [d317700, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36684 p hg
    simpa only [d317700, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317700, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d317700, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36686 (p : Pattern) (guard : d317701 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317701, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d317701, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317700 p = 1 := by simpa only [d317701, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36685 p hg
    simpa only [d317701, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36687 (p : Pattern) (guard : d317702 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317701 p = 1 := by simpa only [d317702, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36686 p hg
    simpa only [d317702, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317702, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d317702, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36688 (p : Pattern) (guard : d316775 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316578 p = 1 := by simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36183 p hg
    simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36679 p hg
    simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36689 (p : Pattern) (guard : d316776 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316775 p = 1 := by simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36688 p hg
    simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36690 (p : Pattern) (guard : d316777 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316776 p = 1 := by simpa only [d316777, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36689 p hg
    simpa only [d316777, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316777, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d316777, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36691 (p : Pattern) (guard : d317703 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317697 p = 1 := by simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36682 p hg
    simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316777 p = 1 := by simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36690 p hg
    simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36692 (p : Pattern) (guard : d317704 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317703 p = 1 := by simpa only [d317704, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36691 p hg
    simpa only [d317704, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317704, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d317704, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36693 (p : Pattern) (guard : d317705 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317704 p = 1 := by simpa only [d317705, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36692 p hg
    simpa only [d317705, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317705, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d317705, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36694 (p : Pattern) (guard : d317706 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317706, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d317706, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317705 p = 1 := by simpa only [d317706, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36693 p hg
    simpa only [d317706, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36695 (p : Pattern) (guard : d317707 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317706 p = 1 := by simpa only [d317707, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36694 p hg
    simpa only [d317707, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317707, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d317707, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36696 (p : Pattern) (guard : d317708 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317702 p = 1 := by simpa only [d317708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36687 p hg
    simpa only [d317708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317707 p = 1 := by simpa only [d317708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36695 p hg
    simpa only [d317708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36697 (p : Pattern) (guard : d316784 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316590 p = 1 := by simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36195 p hg
    simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316777 p = 1 := by simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36690 p hg
    simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36698 (p : Pattern) (guard : d316785 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316784 p = 1 := by simpa only [d316785, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36697 p hg
    simpa only [d316785, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316785, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d316785, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36699 (p : Pattern) (guard : d316786 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316785 p = 1 := by simpa only [d316786, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36698 p hg
    simpa only [d316786, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316786, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d316786, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36700 (p : Pattern) (guard : d316787 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316787, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d316787, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316786 p = 1 := by simpa only [d316787, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36699 p hg
    simpa only [d316787, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36701 (p : Pattern) (guard : d316788 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316787 p = 1 := by simpa only [d316788, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36700 p hg
    simpa only [d316788, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316788, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d316788, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36702 (p : Pattern) (guard : d317709 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317694 p = 1 := by simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36673 p hg
    simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36679 p hg
    simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36703 (p : Pattern) (guard : d258109 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258108 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36679 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36704 (p : Pattern) (guard : d317710 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317709 p = 1 := by simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36702 p hg
    simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36703 p hg
    simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36705 (p : Pattern) (guard : d317711 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317710 p = 1 := by simpa only [d317711, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36704 p hg
    simpa only [d317711, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317711, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d317711, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36706 (p : Pattern) (guard : d317712 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317711 p = 1 := by simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36705 p hg
    simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34881 p hg
    simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36707 (p : Pattern) (guard : d317713 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317712 p = 1 := by simpa only [d317713, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36706 p hg
    simpa only [d317713, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317713, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d317713, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36708 (p : Pattern) (guard : d317714 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317713 p = 1 := by simpa only [d317714, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36707 p hg
    simpa only [d317714, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317714, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d317714, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36709 (p : Pattern) (guard : d317715 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317715, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d317715, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317714 p = 1 := by simpa only [d317715, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36708 p hg
    simpa only [d317715, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36710 (p : Pattern) (guard : d317716 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317715 p = 1 := by simpa only [d317716, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36709 p hg
    simpa only [d317716, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317716, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d317716, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36711 (p : Pattern) (guard : d317717 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316788 p = 1 := by simpa only [d317717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36701 p hg
    simpa only [d317717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317716 p = 1 := by simpa only [d317717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36710 p hg
    simpa only [d317717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36712 (p : Pattern) (guard : d317718 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317708 p = 1 := by simpa only [d317718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36696 p hg
    simpa only [d317718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317717 p = 1 := by simpa only [d317718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36711 p hg
    simpa only [d317718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36713 (p : Pattern) (guard : d317719 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317694 p = 1 := by simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36673 p hg
    simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36714 (p : Pattern) (guard : d317720 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317719 p = 1 := by simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36713 p hg
    simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36703 p hg
    simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36715 (p : Pattern) (guard : d317721 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317720 p = 1 := by simpa only [d317721, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36714 p hg
    simpa only [d317721, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317721, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d317721, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36716 (p : Pattern) (guard : d317722 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317697 p = 1 := by simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36682 p hg
    simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317721 p = 1 := by simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36715 p hg
    simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36717 (p : Pattern) (guard : d317723 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317722 p = 1 := by simpa only [d317723, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36716 p hg
    simpa only [d317723, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317723, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d317723, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36718 (p : Pattern) (guard : d317724 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317723 p = 1 := by simpa only [d317724, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36717 p hg
    simpa only [d317724, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317724, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d317724, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36719 (p : Pattern) (guard : d317725 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317725, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d317725, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317724 p = 1 := by simpa only [d317725, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36718 p hg
    simpa only [d317725, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36720 (p : Pattern) (guard : d317726 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317725 p = 1 := by simpa only [d317726, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36719 p hg
    simpa only [d317726, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317726, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d317726, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36721 (p : Pattern) (guard : d317727 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317721 p = 1 := by simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36715 p hg
    simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34881 p hg
    simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36722 (p : Pattern) (guard : d317728 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317727 p = 1 := by simpa only [d317728, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36721 p hg
    simpa only [d317728, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317728, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d317728, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36723 (p : Pattern) (guard : d317729 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317728 p = 1 := by simpa only [d317729, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36722 p hg
    simpa only [d317729, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317729, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d317729, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36724 (p : Pattern) (guard : d317730 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317730, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d317730, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317729 p = 1 := by simpa only [d317730, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36723 p hg
    simpa only [d317730, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36725 (p : Pattern) (guard : d317731 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317730 p = 1 := by simpa only [d317731, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36724 p hg
    simpa only [d317731, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317731, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d317731, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36726 (p : Pattern) (guard : d317732 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317726 p = 1 := by simpa only [d317732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36720 p hg
    simpa only [d317732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317731 p = 1 := by simpa only [d317732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36725 p hg
    simpa only [d317732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36727 (p : Pattern) (guard : d317733 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317716 p = 1 := by simpa only [d317733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36710 p hg
    simpa only [d317733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d317733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36728 (p : Pattern) (guard : d317734 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317732 p = 1 := by simpa only [d317734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36726 p hg
    simpa only [d317734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317733 p = 1 := by simpa only [d317734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36727 p hg
    simpa only [d317734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36729 (p : Pattern) (guard : d317735 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317718 p = 1 := by simpa only [d317735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36712 p hg
    simpa only [d317735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317734 p = 1 := by simpa only [d317735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36728 p hg
    simpa only [d317735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36730 (p : Pattern) (guard : d317736 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317736, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d317736, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317735 p = 1 := by simpa only [d317736, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36729 p hg
    simpa only [d317736, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36731 (p : Pattern) (guard : d317737 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317737, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d317737, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317736 p = 1 := by simpa only [d317737, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36730 p hg
    simpa only [d317737, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36732 (p : Pattern) (guard : d317738 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317731 p = 1 := by simpa only [d317738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36725 p hg
    simpa only [d317738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d317738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36733 (p : Pattern) (guard : d317739 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317738 p = 1 := by simpa only [d317739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36732 p hg
    simpa only [d317739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d317739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36734 (p : Pattern) (guard : d317740 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317734 p = 1 := by simpa only [d317740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36728 p hg
    simpa only [d317740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317739 p = 1 := by simpa only [d317740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36733 p hg
    simpa only [d317740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36735 (p : Pattern) (guard : d317741 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317741, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d317741, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317740 p = 1 := by simpa only [d317741, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36734 p hg
    simpa only [d317741, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36736 (p : Pattern) (guard : d317742 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317742, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d317742, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317741 p = 1 := by simpa only [d317742, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36735 p hg
    simpa only [d317742, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36737 (p : Pattern) (guard : d317743 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317737 p = 1 := by simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36731 p hg
    simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317742 p = 1 := by simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36736 p hg
    simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36738 (p : Pattern) (guard : d317744 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317742 p = 1 := by simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36736 p hg
    simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36739 (p : Pattern) (guard : d317745 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317743 p = 1 := by simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36737 p hg
    simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317744 p = 1 := by simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36738 p hg
    simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36740 (p : Pattern) (guard : d317746 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317745 p = 1 := by simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36739 p hg
    simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36741 (p : Pattern) (guard : d317747 p = 1) : d50272 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317746 p = 1 := by simpa only [d317747, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36740 p hg
    simpa only [d317747, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317747, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d317747, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36742 (p : Pattern) (guard : d317748 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317748, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d317748, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317747 p = 1 := by simpa only [d317748, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36741 p hg
    simpa only [d317748, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36743 (p : Pattern) (guard : d317749 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317744 p = 1 := by simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36738 p hg
    simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36744 (p : Pattern) (guard : d317750 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317749 p = 1 := by simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36743 p hg
    simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36745 (p : Pattern) (guard : d317751 p = 1) : d50272 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317750 p = 1 := by simpa only [d317751, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36744 p hg
    simpa only [d317751, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317751, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d317751, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36746 (p : Pattern) (guard : d317752 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317752, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d317752, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317751 p = 1 := by simpa only [d317752, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36745 p hg
    simpa only [d317752, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36747 (p : Pattern) (guard : d317753 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317748 p = 1 := by simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36742 p hg
    simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317752 p = 1 := by simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36746 p hg
    simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36748 (p : Pattern) (guard : d317754 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317753 p = 1 := by simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36747 p hg
    simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare36749 (p : Pattern) (guard : d317755 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317754 p = 1 := by simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36748 p hg
    simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
