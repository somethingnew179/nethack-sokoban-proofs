import NetHack.Soko22Hazard87.Compare154
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare38750 (p : Pattern) (guard : d316374 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316373 p = 1 := by simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38749 p hg
    simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38751 (p : Pattern) (guard : d316375 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316374 p = 1 := by simpa only [d316375, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38750 p hg
    simpa only [d316375, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316375, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d316375, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38752 (p : Pattern) (guard : d316376 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316375 p = 1 := by simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38751 p hg
    simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38730 p hg
    simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38753 (p : Pattern) (guard : d316452 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d316452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316376 p = 1 := by simpa only [d316452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38752 p hg
    simpa only [d316452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38754 (p : Pattern) (guard : d316377 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316376 p = 1 := by simpa only [d316377, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38473 p hg
    simpa only [d316377, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316377, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d316377, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38755 (p : Pattern) (guard : d316453 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316452 p = 1 := by simpa only [d316453, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38753 p hg
    simpa only [d316453, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316377 p = 1 := by simpa only [d316453, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38754 p hg
    simpa only [d316453, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38756 (p : Pattern) (guard : d316373 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d286613 p = 1 := by simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38362 p hg
    simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316363 p = 1 := by simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38739 p hg
    simpa only [d316373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38757 (p : Pattern) (guard : d316374 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316373 p = 1 := by simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38756 p hg
    simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d316374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38758 (p : Pattern) (guard : d316375 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316374 p = 1 := by simpa only [d316375, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38757 p hg
    simpa only [d316375, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316375, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d316375, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38759 (p : Pattern) (guard : d316376 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316375 p = 1 := by simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38758 p hg
    simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316366 p = 1 := by simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38742 p hg
    simpa only [d316376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38760 (p : Pattern) (guard : d316377 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316376 p = 1 := by simpa only [d316377, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38759 p hg
    simpa only [d316377, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316377, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d316377, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38761 (p : Pattern) (guard : d316378 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316377 p = 1 := by simpa only [d316378, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38760 p hg
    simpa only [d316378, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316378, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d316378, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38762 (p : Pattern) (guard : d316454 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d316453 p = 1 := by simpa only [d316454, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38755 p hg
    simpa only [d316454, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316378 p = 1 := by simpa only [d316454, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38761 p hg
    simpa only [d316454, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38763 (p : Pattern) (guard : d316455 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316454 p = 1 := by simpa only [d316455, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38762 p hg
    simpa only [d316455, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316455, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d316455, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38764 (p : Pattern) (guard : d317425 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317410 p = 1 := by simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38693 p hg
    simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37966 p hg
    simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38765 (p : Pattern) (guard : d317426 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317425 p = 1 := by simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38764 p hg
    simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37968 p hg
    simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38766 (p : Pattern) (guard : d317427 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317426 p = 1 := by simpa only [d317427, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38765 p hg
    simpa only [d317427, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317427, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d317427, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38767 (p : Pattern) (guard : d317428 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317427 p = 1 := by simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38766 p hg
    simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38768 (p : Pattern) (guard : d317598 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317428 p = 1 := by simpa only [d317598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38767 p hg
    simpa only [d317598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38769 (p : Pattern) (guard : d317429 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317428 p = 1 := by simpa only [d317429, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38481 p hg
    simpa only [d317429, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317429, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317429, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38770 (p : Pattern) (guard : d317599 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317598 p = 1 := by simpa only [d317599, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38768 p hg
    simpa only [d317599, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317429 p = 1 := by simpa only [d317599, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38769 p hg
    simpa only [d317599, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38771 (p : Pattern) (guard : d317425 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317410 p = 1 := by simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38714 p hg
    simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257184 p = 1 := by simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37983 p hg
    simpa only [d317425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38772 (p : Pattern) (guard : d317426 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317425 p = 1 := by simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38771 p hg
    simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37985 p hg
    simpa only [d317426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38773 (p : Pattern) (guard : d317427 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317426 p = 1 := by simpa only [d317427, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38772 p hg
    simpa only [d317427, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317427, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d317427, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38774 (p : Pattern) (guard : d317428 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317427 p = 1 := by simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38773 p hg
    simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37989 p hg
    simpa only [d317428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38775 (p : Pattern) (guard : d317429 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317428 p = 1 := by simpa only [d317429, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38774 p hg
    simpa only [d317429, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317429, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317429, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38776 (p : Pattern) (guard : d317430 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317429 p = 1 := by simpa only [d317430, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38775 p hg
    simpa only [d317430, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317430, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317430, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38777 (p : Pattern) (guard : d317600 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317599 p = 1 := by simpa only [d317600, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38770 p hg
    simpa only [d317600, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317430 p = 1 := by simpa only [d317600, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38776 p hg
    simpa only [d317600, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38778 (p : Pattern) (guard : d317601 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317600 p = 1 := by simpa only [d317601, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38777 p hg
    simpa only [d317601, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317601, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d317601, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38779 (p : Pattern) (guard : d317602 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316455 p = 1 := by simpa only [d317602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38763 p hg
    simpa only [d317602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317601 p = 1 := by simpa only [d317602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38778 p hg
    simpa only [d317602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38780 (p : Pattern) (guard : d317603 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317597 p = 1 := by simpa only [d317603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38748 p hg
    simpa only [d317603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317602 p = 1 := by simpa only [d317603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38779 p hg
    simpa only [d317603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38781 (p : Pattern) (guard : d317435 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317410 p = 1 := by simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38693 p hg
    simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37967 p hg
    simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38782 (p : Pattern) (guard : d317436 p = 1) : d50168 p ≤ (2 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317435 p = 1 := by simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38781 p hg
    simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37968 p hg
    simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38783 (p : Pattern) (guard : d317437 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317436 p = 1 := by simpa only [d317437, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38782 p hg
    simpa only [d317437, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317437, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37970 p hg
    simpa only [d317437, d50210, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38784 (p : Pattern) (guard : d317438 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317413 p = 1 := by simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38696 p hg
    simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317437 p = 1 := by simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38783 p hg
    simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38785 (p : Pattern) (guard : d317613 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317438 p = 1 := by simpa only [d317613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38784 p hg
    simpa only [d317613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38786 (p : Pattern) (guard : d317439 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317438 p = 1 := by simpa only [d317439, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38491 p hg
    simpa only [d317439, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317439, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317439, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38787 (p : Pattern) (guard : d317614 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317613 p = 1 := by simpa only [d317614, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38785 p hg
    simpa only [d317614, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317439 p = 1 := by simpa only [d317614, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38786 p hg
    simpa only [d317614, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38788 (p : Pattern) (guard : d317435 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317410 p = 1 := by simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38714 p hg
    simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37984 p hg
    simpa only [d317435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38789 (p : Pattern) (guard : d317436 p = 1) : d50211 p ≤ (2 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317435 p = 1 := by simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38788 p hg
    simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257185 p = 1 := by simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37985 p hg
    simpa only [d317436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38790 (p : Pattern) (guard : d317437 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317436 p = 1 := by simpa only [d317437, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38789 p hg
    simpa only [d317437, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317437, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37987 p hg
    simpa only [d317437, d50212, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38791 (p : Pattern) (guard : d317438 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317413 p = 1 := by simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38717 p hg
    simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317437 p = 1 := by simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38790 p hg
    simpa only [d317438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38792 (p : Pattern) (guard : d317439 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317438 p = 1 := by simpa only [d317439, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38791 p hg
    simpa only [d317439, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317439, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317439, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38793 (p : Pattern) (guard : d317440 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317439 p = 1 := by simpa only [d317440, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38792 p hg
    simpa only [d317440, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317440, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317440, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38794 (p : Pattern) (guard : d317615 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317614 p = 1 := by simpa only [d317615, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38787 p hg
    simpa only [d317615, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317440 p = 1 := by simpa only [d317615, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38793 p hg
    simpa only [d317615, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38795 (p : Pattern) (guard : d317616 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317615 p = 1 := by simpa only [d317616, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38794 p hg
    simpa only [d317616, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317616, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d317616, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38796 (p : Pattern) (guard : d317443 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317437 p = 1 := by simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38783 p hg
    simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38797 (p : Pattern) (guard : d317617 p = 1) : d50210 p ≤ (2 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37958 p hg
    simpa only [d317617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317443 p = 1 := by simpa only [d317617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38796 p hg
    simpa only [d317617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38798 (p : Pattern) (guard : d317444 p = 1) : d50420 p ≤ (2 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317443 p = 1 := by simpa only [d317444, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38496 p hg
    simpa only [d317444, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317444, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37919 p hg
    simpa only [d317444, d50420, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38799 (p : Pattern) (guard : d317618 p = 1) : d50421 p ≤ (2 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317617 p = 1 := by simpa only [d317618, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38797 p hg
    simpa only [d317618, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317444 p = 1 := by simpa only [d317618, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38798 p hg
    simpa only [d317618, d50421, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38800 (p : Pattern) (guard : d317443 p = 1) : d50212 p ≤ (2 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317437 p = 1 := by simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38790 p hg
    simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37989 p hg
    simpa only [d317443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38801 (p : Pattern) (guard : d317444 p = 1) : d50223 p ≤ (2 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317443 p = 1 := by simpa only [d317444, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38800 p hg
    simpa only [d317444, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317444, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317444, d50223, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38802 (p : Pattern) (guard : d317445 p = 1) : d50224 p ≤ (2 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317444 p = 1 := by simpa only [d317445, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38801 p hg
    simpa only [d317445, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317445, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37921 p hg
    simpa only [d317445, d50224, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38803 (p : Pattern) (guard : d317619 p = 1) : d50422 p ≤ (2 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d317618 p = 1 := by simpa only [d317619, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38799 p hg
    simpa only [d317619, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317445 p = 1 := by simpa only [d317619, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38802 p hg
    simpa only [d317619, d50422, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38804 (p : Pattern) (guard : d317620 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317619 p = 1 := by simpa only [d317620, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38803 p hg
    simpa only [d317620, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317620, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37994 p hg
    simpa only [d317620, d50426, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38805 (p : Pattern) (guard : d317621 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317616 p = 1 := by simpa only [d317621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38795 p hg
    simpa only [d317621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317620 p = 1 := by simpa only [d317621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38804 p hg
    simpa only [d317621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38806 (p : Pattern) (guard : d317607 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317601 p = 1 := by simpa only [d317607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38778 p hg
    simpa only [d317607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37996 p hg
    simpa only [d317607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38807 (p : Pattern) (guard : d317622 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317621 p = 1 := by simpa only [d317622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38805 p hg
    simpa only [d317622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317607 p = 1 := by simpa only [d317622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38806 p hg
    simpa only [d317622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38808 (p : Pattern) (guard : d317623 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317603 p = 1 := by simpa only [d317623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38780 p hg
    simpa only [d317623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317622 p = 1 := by simpa only [d317623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38807 p hg
    simpa only [d317623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38809 (p : Pattern) (guard : d317624 p = 1) : d50427 p ≤ (2 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317624, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37957 p hg
    simpa only [d317624, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317623 p = 1 := by simpa only [d317624, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38808 p hg
    simpa only [d317624, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38810 (p : Pattern) (guard : d317625 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317625, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37956 p hg
    simpa only [d317625, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317624 p = 1 := by simpa only [d317625, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38809 p hg
    simpa only [d317625, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38811 (p : Pattern) (guard : d317626 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317620 p = 1 := by simpa only [d317626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38804 p hg
    simpa only [d317626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37996 p hg
    simpa only [d317626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38812 (p : Pattern) (guard : d317627 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317626 p = 1 := by simpa only [d317627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38811 p hg
    simpa only [d317627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37996 p hg
    simpa only [d317627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38813 (p : Pattern) (guard : d317628 p = 1) : d50426 p ≤ (2 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317622 p = 1 := by simpa only [d317628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38807 p hg
    simpa only [d317628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317627 p = 1 := by simpa only [d317628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38812 p hg
    simpa only [d317628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38814 (p : Pattern) (guard : d317629 p = 1) : d50427 p ≤ (2 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317629, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37957 p hg
    simpa only [d317629, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317628 p = 1 := by simpa only [d317629, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38813 p hg
    simpa only [d317629, d50427, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38815 (p : Pattern) (guard : d317630 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317630, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37956 p hg
    simpa only [d317630, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317629 p = 1 := by simpa only [d317630, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38814 p hg
    simpa only [d317630, d50428, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38816 (p : Pattern) (guard : d317631 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317625 p = 1 := by simpa only [d317631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38810 p hg
    simpa only [d317631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317630 p = 1 := by simpa only [d317631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38815 p hg
    simpa only [d317631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38817 (p : Pattern) (guard : d317636 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317630 p = 1 := by simpa only [d317636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38815 p hg
    simpa only [d317636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d317636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38818 (p : Pattern) (guard : d317637 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317631 p = 1 := by simpa only [d317637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38816 p hg
    simpa only [d317637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317636 p = 1 := by simpa only [d317637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38817 p hg
    simpa only [d317637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38819 (p : Pattern) (guard : d317638 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317637 p = 1 := by simpa only [d317638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38818 p hg
    simpa only [d317638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d317638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38820 (p : Pattern) (guard : d317639 p = 1) : d50430 p ≤ (2 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317638 p = 1 := by simpa only [d317639, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38819 p hg
    simpa only [d317639, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317639, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38006 p hg
    simpa only [d317639, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38821 (p : Pattern) (guard : d317640 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317640, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d317640, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317639 p = 1 := by simpa only [d317640, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38820 p hg
    simpa only [d317640, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38822 (p : Pattern) (guard : d317645 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317636 p = 1 := by simpa only [d317645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38817 p hg
    simpa only [d317645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d317645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38823 (p : Pattern) (guard : d317646 p = 1) : d50428 p ≤ (2 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317645 p = 1 := by simpa only [d317646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38822 p hg
    simpa only [d317646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38002 p hg
    simpa only [d317646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38824 (p : Pattern) (guard : d317647 p = 1) : d50430 p ≤ (2 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317646 p = 1 := by simpa only [d317647, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38823 p hg
    simpa only [d317647, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317647, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38006 p hg
    simpa only [d317647, d50430, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38825 (p : Pattern) (guard : d317648 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317648, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d317648, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317647 p = 1 := by simpa only [d317648, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38824 p hg
    simpa only [d317648, d50431, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38826 (p : Pattern) (guard : d317649 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317640 p = 1 := by simpa only [d317649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38821 p hg
    simpa only [d317649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317648 p = 1 := by simpa only [d317649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38825 p hg
    simpa only [d317649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38827 (p : Pattern) (guard : d317650 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317649 p = 1 := by simpa only [d317650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38826 p hg
    simpa only [d317650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d317650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38828 (p : Pattern) (guard : d317651 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317650 p = 1 := by simpa only [d317651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38827 p hg
    simpa only [d317651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d317651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38829 (p : Pattern) (guard : d317652 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317651 p = 1 := by simpa only [d317652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38828 p hg
    simpa only [d317652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d317652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38830 (p : Pattern) (guard : d317666 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317648 p = 1 := by simpa only [d317666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38825 p hg
    simpa only [d317666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d317666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38831 (p : Pattern) (guard : d317667 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317666 p = 1 := by simpa only [d317667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38830 p hg
    simpa only [d317667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d317667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38832 (p : Pattern) (guard : d317668 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317667 p = 1 := by simpa only [d317668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38831 p hg
    simpa only [d317668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d317668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38833 (p : Pattern) (guard : d317669 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317668 p = 1 := by simpa only [d317669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38832 p hg
    simpa only [d317669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d317669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38834 (p : Pattern) (guard : d318424 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317652 p = 1 := by simpa only [d318424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38829 p hg
    simpa only [d318424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317669 p = 1 := by simpa only [d318424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38833 p hg
    simpa only [d318424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38835 (p : Pattern) (guard : d318425 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318424 p = 1 := by simpa only [d318425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38834 p hg
    simpa only [d318425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38836 (p : Pattern) (guard : d318426 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d318425 p = 1 := by simpa only [d318426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38835 p hg
    simpa only [d318426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38837 (p : Pattern) (guard : d318427 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318426 p = 1 := by simpa only [d318427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38836 p hg
    simpa only [d318427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38838 (p : Pattern) (guard : d318428 p = 1) : d50431 p ≤ (2 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37955 p hg
    simpa only [d318428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318427 p = 1 := by simpa only [d318428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38837 p hg
    simpa only [d318428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38839 (p : Pattern) (guard : d318429 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318429, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d318429, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318428 p = 1 := by simpa only [d318429, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38838 p hg
    simpa only [d318429, d50432, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38840 (p : Pattern) (guard : d318430 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d318430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318429 p = 1 := by simpa only [d318430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38839 p hg
    simpa only [d318430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38841 (p : Pattern) (guard : d318431 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d318430 p = 1 := by simpa only [d318431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38840 p hg
    simpa only [d318431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d318431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38842 (p : Pattern) (guard : d318432 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d318431 p = 1 := by simpa only [d318432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38841 p hg
    simpa only [d318432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d318432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38843 (p : Pattern) (guard : d318433 p = 1) : d50432 p ≤ (2 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d318432 p = 1 := by simpa only [d318433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38842 p hg
    simpa only [d318433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37954 p hg
    simpa only [d318433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38844 (p : Pattern) (guard : d318434 p = 1) : d50492 p ≤ (2 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d318433 p = 1 := by simpa only [d318434, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38843 p hg
    simpa only [d318434, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318434, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38023 p hg
    simpa only [d318434, d50492, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38845 (p : Pattern) (guard : d318435 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d318423 p = 1 := by simpa only [d318435, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38679 p hg
    simpa only [d318435, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318434 p = 1 := by simpa only [d318435, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38844 p hg
    simpa only [d318435, d50493, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38846 (p : Pattern) (guard : d318436 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318435 p = 1 := by simpa only [d318436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38845 p hg
    simpa only [d318436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38847 (p : Pattern) (guard : d318437 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318436 p = 1 := by simpa only [d318437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38846 p hg
    simpa only [d318437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38848 (p : Pattern) (guard : d318438 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318437 p = 1 := by simpa only [d318438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38847 p hg
    simpa only [d318438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38849 (p : Pattern) (guard : d318439 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318438 p = 1 := by simpa only [d318439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38848 p hg
    simpa only [d318439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38850 (p : Pattern) (guard : d318440 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318439 p = 1 := by simpa only [d318440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38849 p hg
    simpa only [d318440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38851 (p : Pattern) (guard : d318441 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318440 p = 1 := by simpa only [d318441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38850 p hg
    simpa only [d318441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38852 (p : Pattern) (guard : d318442 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318441 p = 1 := by simpa only [d318442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38851 p hg
    simpa only [d318442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38853 (p : Pattern) (guard : d318443 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37816 p hg
    simpa only [d318443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318442 p = 1 := by simpa only [d318443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38852 p hg
    simpa only [d318443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38854 (p : Pattern) (guard : d318444 p = 1) : d50493 p ≤ (2 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d318255 p = 1 := by simpa only [d318444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38433 p hg
    simpa only [d318444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318443 p = 1 := by simpa only [d318444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38853 p hg
    simpa only [d318444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38855 (p : Pattern) (guard : d34355 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34354 p = 1 := by simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38439 p hg
    simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38856 (p : Pattern) (guard : d34356 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34355 p = 1 := by simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38855 p hg
    simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38857 (p : Pattern) (guard : d34357 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d34356 p = 1 := by simpa only [d34357, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38856 p hg
    simpa only [d34357, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34357, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d34357, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38858 (p : Pattern) (guard : d40834 p = 1) : d47617 p ≤ (2 : Int) + d47617 p := by
  omega
theorem compare38859 (p : Pattern) (guard : d317691 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d40834 p = 1 := by simpa only [d317691, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38858 p hg
    simpa only [d317691, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317691, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37826 p hg
    simpa only [d317691, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38860 (p : Pattern) (guard : d317692 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317691 p = 1 := by simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38859 p hg
    simpa only [d317692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38861 (p : Pattern) (guard : d317693 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d317692 p = 1 := by simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38860 p hg
    simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d317693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38862 (p : Pattern) (guard : d317694 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d317693 p = 1 := by simpa only [d317694, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38861 p hg
    simpa only [d317694, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317694, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37830 p hg
    simpa only [d317694, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38863 (p : Pattern) (guard : d317695 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317694 p = 1 := by simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38862 p hg
    simpa only [d317695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38864 (p : Pattern) (guard : d1531 p = 1) : d47617 p ≤ (2 : Int) + d47617 p := by
  omega
theorem compare38865 (p : Pattern) (guard : d1547 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38864 p hg
    simpa only [d1547, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37826 p hg
    simpa only [d1547, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38866 (p : Pattern) (guard : d39244 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38865 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38867 (p : Pattern) (guard : d258107 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d39244 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38866 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38868 (p : Pattern) (guard : d258108 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258107 p = 1 := by simpa only [d258108, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38867 p hg
    simpa only [d258108, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258108, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37830 p hg
    simpa only [d258108, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38869 (p : Pattern) (guard : d316767 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d34354 p = 1 := by simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38439 p hg
    simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38868 p hg
    simpa only [d316767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38870 (p : Pattern) (guard : d317696 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317695 p = 1 := by simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38863 p hg
    simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316767 p = 1 := by simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38869 p hg
    simpa only [d317696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38871 (p : Pattern) (guard : d317697 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317696 p = 1 := by simpa only [d317697, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38870 p hg
    simpa only [d317697, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317697, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d317697, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38872 (p : Pattern) (guard : d317698 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d34357 p = 1 := by simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38857 p hg
    simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317697 p = 1 := by simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38871 p hg
    simpa only [d317698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38873 (p : Pattern) (guard : d317699 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317698 p = 1 := by simpa only [d317699, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38872 p hg
    simpa only [d317699, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317699, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d317699, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38874 (p : Pattern) (guard : d317700 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317699 p = 1 := by simpa only [d317700, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38873 p hg
    simpa only [d317700, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317700, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d317700, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38875 (p : Pattern) (guard : d317701 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317701, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d317701, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317700 p = 1 := by simpa only [d317701, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38874 p hg
    simpa only [d317701, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38876 (p : Pattern) (guard : d317702 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317701 p = 1 := by simpa only [d317702, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38875 p hg
    simpa only [d317702, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317702, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d317702, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38877 (p : Pattern) (guard : d34366 p = 1) : d47617 p ≤ (2 : Int) + d47617 p := by
  omega
theorem compare38878 (p : Pattern) (guard : d34367 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d34366 p = 1 := by simpa only [d34367, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38877 p hg
    simpa only [d34367, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34367, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37826 p hg
    simpa only [d34367, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38879 (p : Pattern) (guard : d316576 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34367 p = 1 := by simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38878 p hg
    simpa only [d316576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38880 (p : Pattern) (guard : d316577 p = 1) : d50119 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d316576 p = 1 := by simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38879 p hg
    simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37824 p hg
    simpa only [d316577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38881 (p : Pattern) (guard : d316578 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d316577 p = 1 := by simpa only [d316578, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38880 p hg
    simpa only [d316578, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316578, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37830 p hg
    simpa only [d316578, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38882 (p : Pattern) (guard : d316775 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d316578 p = 1 := by simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38881 p hg
    simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38868 p hg
    simpa only [d316775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38883 (p : Pattern) (guard : d316776 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316775 p = 1 := by simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38882 p hg
    simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d316776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38884 (p : Pattern) (guard : d316777 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316776 p = 1 := by simpa only [d316777, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38883 p hg
    simpa only [d316777, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316777, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d316777, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38885 (p : Pattern) (guard : d317703 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317697 p = 1 := by simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38871 p hg
    simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316777 p = 1 := by simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38884 p hg
    simpa only [d317703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38886 (p : Pattern) (guard : d317704 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317703 p = 1 := by simpa only [d317704, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38885 p hg
    simpa only [d317704, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317704, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d317704, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38887 (p : Pattern) (guard : d317705 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317704 p = 1 := by simpa only [d317705, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38886 p hg
    simpa only [d317705, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317705, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d317705, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38888 (p : Pattern) (guard : d317706 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317706, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d317706, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317705 p = 1 := by simpa only [d317706, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38887 p hg
    simpa only [d317706, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38889 (p : Pattern) (guard : d317707 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317706 p = 1 := by simpa only [d317707, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38888 p hg
    simpa only [d317707, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317707, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d317707, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38890 (p : Pattern) (guard : d317708 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317702 p = 1 := by simpa only [d317708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38876 p hg
    simpa only [d317708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317707 p = 1 := by simpa only [d317708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38889 p hg
    simpa only [d317708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38891 (p : Pattern) (guard : d316588 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316578 p = 1 := by simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38881 p hg
    simpa only [d316588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38892 (p : Pattern) (guard : d316589 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d316588 p = 1 := by simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38891 p hg
    simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d316589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38893 (p : Pattern) (guard : d316590 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d316589 p = 1 := by simpa only [d316590, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38892 p hg
    simpa only [d316590, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316590, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d316590, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38894 (p : Pattern) (guard : d316784 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d316590 p = 1 := by simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38893 p hg
    simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316777 p = 1 := by simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38884 p hg
    simpa only [d316784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38895 (p : Pattern) (guard : d316785 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d316784 p = 1 := by simpa only [d316785, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38894 p hg
    simpa only [d316785, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316785, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d316785, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38896 (p : Pattern) (guard : d316786 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d316785 p = 1 := by simpa only [d316786, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38895 p hg
    simpa only [d316786, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316786, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d316786, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38897 (p : Pattern) (guard : d316787 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d316787, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d316787, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d316786 p = 1 := by simpa only [d316787, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38896 p hg
    simpa only [d316787, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38898 (p : Pattern) (guard : d316788 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d316787 p = 1 := by simpa only [d316788, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38897 p hg
    simpa only [d316788, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d316788, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d316788, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38899 (p : Pattern) (guard : d317709 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317694 p = 1 := by simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38862 p hg
    simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258108 p = 1 := by simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38868 p hg
    simpa only [d317709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38900 (p : Pattern) (guard : d258109 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258108 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38868 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38901 (p : Pattern) (guard : d317710 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317709 p = 1 := by simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38899 p hg
    simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38900 p hg
    simpa only [d317710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38902 (p : Pattern) (guard : d317711 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317710 p = 1 := by simpa only [d317711, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38901 p hg
    simpa only [d317711, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317711, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d317711, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38903 (p : Pattern) (guard : d317712 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317711 p = 1 := by simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38902 p hg
    simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37837 p hg
    simpa only [d317712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38904 (p : Pattern) (guard : d317713 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317712 p = 1 := by simpa only [d317713, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38903 p hg
    simpa only [d317713, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317713, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d317713, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38905 (p : Pattern) (guard : d317714 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317713 p = 1 := by simpa only [d317714, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38904 p hg
    simpa only [d317714, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317714, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d317714, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38906 (p : Pattern) (guard : d317715 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317715, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d317715, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317714 p = 1 := by simpa only [d317715, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38905 p hg
    simpa only [d317715, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38907 (p : Pattern) (guard : d317716 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317715 p = 1 := by simpa only [d317716, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38906 p hg
    simpa only [d317716, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317716, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d317716, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38908 (p : Pattern) (guard : d317717 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d316788 p = 1 := by simpa only [d317717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38898 p hg
    simpa only [d317717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317716 p = 1 := by simpa only [d317717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38907 p hg
    simpa only [d317717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38909 (p : Pattern) (guard : d317718 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317708 p = 1 := by simpa only [d317718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38890 p hg
    simpa only [d317718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317717 p = 1 := by simpa only [d317718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38908 p hg
    simpa only [d317718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38910 (p : Pattern) (guard : d317719 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d317694 p = 1 := by simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38862 p hg
    simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37832 p hg
    simpa only [d317719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38911 (p : Pattern) (guard : d317720 p = 1) : d50122 p ≤ (2 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d317719 p = 1 := by simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38910 p hg
    simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38900 p hg
    simpa only [d317720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38912 (p : Pattern) (guard : d317721 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d317720 p = 1 := by simpa only [d317721, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38911 p hg
    simpa only [d317721, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317721, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37835 p hg
    simpa only [d317721, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38913 (p : Pattern) (guard : d317722 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317697 p = 1 := by simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38871 p hg
    simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317721 p = 1 := by simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38912 p hg
    simpa only [d317722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38914 (p : Pattern) (guard : d317723 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317722 p = 1 := by simpa only [d317723, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38913 p hg
    simpa only [d317723, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317723, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d317723, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38915 (p : Pattern) (guard : d317724 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317723 p = 1 := by simpa only [d317724, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38914 p hg
    simpa only [d317724, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317724, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d317724, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38916 (p : Pattern) (guard : d317725 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317725, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d317725, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317724 p = 1 := by simpa only [d317725, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38915 p hg
    simpa only [d317725, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38917 (p : Pattern) (guard : d317726 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317725 p = 1 := by simpa only [d317726, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38916 p hg
    simpa only [d317726, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317726, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d317726, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38918 (p : Pattern) (guard : d317727 p = 1) : d50202 p ≤ (2 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d317721 p = 1 := by simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38912 p hg
    simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37837 p hg
    simpa only [d317727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38919 (p : Pattern) (guard : d317728 p = 1) : d50220 p ≤ (2 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d317727 p = 1 := by simpa only [d317728, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38918 p hg
    simpa only [d317728, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317728, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37839 p hg
    simpa only [d317728, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38920 (p : Pattern) (guard : d317729 p = 1) : d50221 p ≤ (2 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d317728 p = 1 := by simpa only [d317729, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38919 p hg
    simpa only [d317729, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317729, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37841 p hg
    simpa only [d317729, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38921 (p : Pattern) (guard : d317730 p = 1) : d50222 p ≤ (2 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317730, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37823 p hg
    simpa only [d317730, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317729 p = 1 := by simpa only [d317730, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38920 p hg
    simpa only [d317730, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38922 (p : Pattern) (guard : d317731 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d317730 p = 1 := by simpa only [d317731, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38921 p hg
    simpa only [d317731, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317731, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37844 p hg
    simpa only [d317731, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38923 (p : Pattern) (guard : d317732 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317726 p = 1 := by simpa only [d317732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38917 p hg
    simpa only [d317732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317731 p = 1 := by simpa only [d317732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38922 p hg
    simpa only [d317732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38924 (p : Pattern) (guard : d317733 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317716 p = 1 := by simpa only [d317733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38907 p hg
    simpa only [d317733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37846 p hg
    simpa only [d317733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38925 (p : Pattern) (guard : d317734 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317732 p = 1 := by simpa only [d317734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38923 p hg
    simpa only [d317734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317733 p = 1 := by simpa only [d317734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38924 p hg
    simpa only [d317734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38926 (p : Pattern) (guard : d317735 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317718 p = 1 := by simpa only [d317735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38909 p hg
    simpa only [d317735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317734 p = 1 := by simpa only [d317735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38925 p hg
    simpa only [d317735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38927 (p : Pattern) (guard : d317736 p = 1) : d50227 p ≤ (2 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317736, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37822 p hg
    simpa only [d317736, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317735 p = 1 := by simpa only [d317736, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38926 p hg
    simpa only [d317736, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38928 (p : Pattern) (guard : d317737 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317737, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37821 p hg
    simpa only [d317737, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317736 p = 1 := by simpa only [d317737, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38927 p hg
    simpa only [d317737, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38929 (p : Pattern) (guard : d317738 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d317731 p = 1 := by simpa only [d317738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38922 p hg
    simpa only [d317738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37846 p hg
    simpa only [d317738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38930 (p : Pattern) (guard : d317739 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d317738 p = 1 := by simpa only [d317739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38929 p hg
    simpa only [d317739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37846 p hg
    simpa only [d317739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38931 (p : Pattern) (guard : d317740 p = 1) : d50226 p ≤ (2 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d317734 p = 1 := by simpa only [d317740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38925 p hg
    simpa only [d317740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317739 p = 1 := by simpa only [d317740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38930 p hg
    simpa only [d317740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38932 (p : Pattern) (guard : d317741 p = 1) : d50227 p ≤ (2 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317741, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37822 p hg
    simpa only [d317741, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317740 p = 1 := by simpa only [d317741, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38931 p hg
    simpa only [d317741, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38933 (p : Pattern) (guard : d317742 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317742, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37821 p hg
    simpa only [d317742, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317741 p = 1 := by simpa only [d317742, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38932 p hg
    simpa only [d317742, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38934 (p : Pattern) (guard : d317743 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317737 p = 1 := by simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38928 p hg
    simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317742 p = 1 := by simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38933 p hg
    simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38935 (p : Pattern) (guard : d317744 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317742 p = 1 := by simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38933 p hg
    simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38936 (p : Pattern) (guard : d317745 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317743 p = 1 := by simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38934 p hg
    simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317744 p = 1 := by simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38935 p hg
    simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38937 (p : Pattern) (guard : d317746 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317745 p = 1 := by simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38936 p hg
    simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38938 (p : Pattern) (guard : d317747 p = 1) : d50272 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317746 p = 1 := by simpa only [d317747, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38937 p hg
    simpa only [d317747, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317747, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d317747, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38939 (p : Pattern) (guard : d317748 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317748, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d317748, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317747 p = 1 := by simpa only [d317748, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38938 p hg
    simpa only [d317748, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38940 (p : Pattern) (guard : d317749 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317744 p = 1 := by simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38935 p hg
    simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38941 (p : Pattern) (guard : d317750 p = 1) : d50271 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317749 p = 1 := by simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38940 p hg
    simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37852 p hg
    simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38942 (p : Pattern) (guard : d317751 p = 1) : d50272 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317750 p = 1 := by simpa only [d317751, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38941 p hg
    simpa only [d317751, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317751, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d317751, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38943 (p : Pattern) (guard : d317752 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317752, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37820 p hg
    simpa only [d317752, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317751 p = 1 := by simpa only [d317752, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38942 p hg
    simpa only [d317752, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38944 (p : Pattern) (guard : d317753 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317748 p = 1 := by simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38939 p hg
    simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317752 p = 1 := by simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38943 p hg
    simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38945 (p : Pattern) (guard : d317754 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317753 p = 1 := by simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38944 p hg
    simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38946 (p : Pattern) (guard : d317755 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317754 p = 1 := by simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38945 p hg
    simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38947 (p : Pattern) (guard : d317756 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317755 p = 1 := by simpa only [d317756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38946 p hg
    simpa only [d317756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38948 (p : Pattern) (guard : d317757 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317752 p = 1 := by simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38943 p hg
    simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38949 (p : Pattern) (guard : d317758 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317757 p = 1 := by simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38948 p hg
    simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38950 (p : Pattern) (guard : d317759 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317758 p = 1 := by simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38949 p hg
    simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38951 (p : Pattern) (guard : d317760 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317759 p = 1 := by simpa only [d317760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38950 p hg
    simpa only [d317760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38952 (p : Pattern) (guard : d317761 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317756 p = 1 := by simpa only [d317761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38947 p hg
    simpa only [d317761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317760 p = 1 := by simpa only [d317761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38951 p hg
    simpa only [d317761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38953 (p : Pattern) (guard : d317762 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317761 p = 1 := by simpa only [d317762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38952 p hg
    simpa only [d317762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38954 (p : Pattern) (guard : d317763 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317762 p = 1 := by simpa only [d317763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38953 p hg
    simpa only [d317763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38955 (p : Pattern) (guard : d317764 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317763 p = 1 := by simpa only [d317764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38954 p hg
    simpa only [d317764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38956 (p : Pattern) (guard : d317765 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317764 p = 1 := by simpa only [d317765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38955 p hg
    simpa only [d317765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38957 (p : Pattern) (guard : d317766 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317766, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317766, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317765 p = 1 := by simpa only [d317766, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38956 p hg
    simpa only [d317766, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38958 (p : Pattern) (guard : d317737 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317737, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37870 p hg
    simpa only [d317737, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317736 p = 1 := by simpa only [d317737, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38927 p hg
    simpa only [d317737, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38959 (p : Pattern) (guard : d317742 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317742, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37870 p hg
    simpa only [d317742, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317741 p = 1 := by simpa only [d317742, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38932 p hg
    simpa only [d317742, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38960 (p : Pattern) (guard : d317743 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317737 p = 1 := by simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38958 p hg
    simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317742 p = 1 := by simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38959 p hg
    simpa only [d317743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38961 (p : Pattern) (guard : d317744 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d317742 p = 1 := by simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38959 p hg
    simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d317744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38962 (p : Pattern) (guard : d317745 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317743 p = 1 := by simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38960 p hg
    simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317744 p = 1 := by simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38961 p hg
    simpa only [d317745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38963 (p : Pattern) (guard : d317746 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317745 p = 1 := by simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38962 p hg
    simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d317746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38964 (p : Pattern) (guard : d317747 p = 1) : d50250 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317746 p = 1 := by simpa only [d317747, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38963 p hg
    simpa only [d317747, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317747, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d317747, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38965 (p : Pattern) (guard : d317748 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317748, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37869 p hg
    simpa only [d317748, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317747 p = 1 := by simpa only [d317748, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38964 p hg
    simpa only [d317748, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38966 (p : Pattern) (guard : d317749 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d317744 p = 1 := by simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38961 p hg
    simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d317749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38967 (p : Pattern) (guard : d317750 p = 1) : d50248 p ≤ (2 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d317749 p = 1 := by simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38966 p hg
    simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37872 p hg
    simpa only [d317750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38968 (p : Pattern) (guard : d317751 p = 1) : d50250 p ≤ (2 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d317750 p = 1 := by simpa only [d317751, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38967 p hg
    simpa only [d317751, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317751, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37856 p hg
    simpa only [d317751, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38969 (p : Pattern) (guard : d317752 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317752, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37869 p hg
    simpa only [d317752, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317751 p = 1 := by simpa only [d317752, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38968 p hg
    simpa only [d317752, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38970 (p : Pattern) (guard : d317753 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317748 p = 1 := by simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38965 p hg
    simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317752 p = 1 := by simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38969 p hg
    simpa only [d317753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38971 (p : Pattern) (guard : d317754 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317753 p = 1 := by simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38970 p hg
    simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38972 (p : Pattern) (guard : d317755 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317754 p = 1 := by simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38971 p hg
    simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38973 (p : Pattern) (guard : d317756 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317755 p = 1 := by simpa only [d317756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38972 p hg
    simpa only [d317756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38974 (p : Pattern) (guard : d317757 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d317752 p = 1 := by simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38969 p hg
    simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38975 (p : Pattern) (guard : d317758 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d317757 p = 1 := by simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38974 p hg
    simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38976 (p : Pattern) (guard : d317759 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d317758 p = 1 := by simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38975 p hg
    simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38977 (p : Pattern) (guard : d317760 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317759 p = 1 := by simpa only [d317760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38976 p hg
    simpa only [d317760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38978 (p : Pattern) (guard : d317761 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317756 p = 1 := by simpa only [d317761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38973 p hg
    simpa only [d317761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317760 p = 1 := by simpa only [d317761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38977 p hg
    simpa only [d317761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38979 (p : Pattern) (guard : d317762 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317761 p = 1 := by simpa only [d317762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38978 p hg
    simpa only [d317762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38980 (p : Pattern) (guard : d317763 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317762 p = 1 := by simpa only [d317763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38979 p hg
    simpa only [d317763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38981 (p : Pattern) (guard : d317764 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317763 p = 1 := by simpa only [d317764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38980 p hg
    simpa only [d317764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38982 (p : Pattern) (guard : d317765 p = 1) : d50251 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37818 p hg
    simpa only [d317765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317764 p = 1 := by simpa only [d317765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38981 p hg
    simpa only [d317765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38983 (p : Pattern) (guard : d317769 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317755 p = 1 := by simpa only [d317769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38946 p hg
    simpa only [d317769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38984 (p : Pattern) (guard : d317770 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d317759 p = 1 := by simpa only [d317770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38950 p hg
    simpa only [d317770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38985 (p : Pattern) (guard : d317771 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d317769 p = 1 := by simpa only [d317771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38983 p hg
    simpa only [d317771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317770 p = 1 := by simpa only [d317771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38984 p hg
    simpa only [d317771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38986 (p : Pattern) (guard : d317772 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317771 p = 1 := by simpa only [d317772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38985 p hg
    simpa only [d317772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38987 (p : Pattern) (guard : d317773 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d317772 p = 1 := by simpa only [d317773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38986 p hg
    simpa only [d317773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38988 (p : Pattern) (guard : d317774 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317773 p = 1 := by simpa only [d317774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38987 p hg
    simpa only [d317774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38989 (p : Pattern) (guard : d317775 p = 1) : d50273 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d317775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37819 p hg
    simpa only [d317775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317774 p = 1 := by simpa only [d317775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38988 p hg
    simpa only [d317775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38990 (p : Pattern) (guard : d317776 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d317765 p = 1 := by simpa only [d317776, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38982 p hg
    simpa only [d317776, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317775 p = 1 := by simpa only [d317776, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38989 p hg
    simpa only [d317776, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38991 (p : Pattern) (guard : d317777 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d317766 p = 1 := by simpa only [d317777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38957 p hg
    simpa only [d317777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317776 p = 1 := by simpa only [d317777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38990 p hg
    simpa only [d317777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38992 (p : Pattern) (guard : d317778 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d317777 p = 1 := by simpa only [d317778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38991 p hg
    simpa only [d317778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d317778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38993 (p : Pattern) (guard : d318445 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d317778 p = 1 := by simpa only [d318445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38992 p hg
    simpa only [d318445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d318445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d318445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38994 (p : Pattern) (guard : d318446 p = 1) : d50274 p ≤ (2 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d318446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37817 p hg
    simpa only [d318446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d318445 p = 1 := by simpa only [d318446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38993 p hg
    simpa only [d318446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38995 (p : Pattern) (guard : d34355 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34354 p = 1 := by simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38578 p hg
    simpa only [d34355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38996 (p : Pattern) (guard : d34356 p = 1) : d50291 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37912 p hg
    simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d34355 p = 1 := by simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38995 p hg
    simpa only [d34356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38997 (p : Pattern) (guard : d34357 p = 1) : d50347 p ≤ (2 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d34356 p = 1 := by simpa only [d34357, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38996 p hg
    simpa only [d34357, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34357, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37915 p hg
    simpa only [d34357, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38998 (p : Pattern) (guard : d40834 p = 1) : d47706 p ≤ (2 : Int) + d47706 p := by
  omega
theorem compare38999 (p : Pattern) (guard : d317691 p = 1) : d50288 p ≤ (2 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d40834 p = 1 := by simpa only [d317691, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38998 p hg
    simpa only [d317691, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d317691, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37906 p hg
    simpa only [d317691, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
