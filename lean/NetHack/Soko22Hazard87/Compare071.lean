import NetHack.Soko22Hazard87.Compare070
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare17750 (p : Pattern) (guard : d2342 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17751 (p : Pattern) (guard : d2343 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2342 p = 1 := by simpa only [d2343, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17750 p hg
    simpa only [d2343, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2343, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d2343, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17752 (p : Pattern) (guard : d17393 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17753 (p : Pattern) (guard : d17394 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d17393 p = 1 := by simpa only [d17394, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17752 p hg
    simpa only [d17394, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17394, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d17394, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17754 (p : Pattern) (guard : d17395 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2343 p = 1 := by simpa only [d17395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17751 p hg
    simpa only [d17395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17394 p = 1 := by simpa only [d17395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17753 p hg
    simpa only [d17395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17755 (p : Pattern) (guard : d15779 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15778 p = 1 := by simpa only [d15779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17747 p hg
    simpa only [d15779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d15779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17756 (p : Pattern) (guard : d17396 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d17395 p = 1 := by simpa only [d17396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17754 p hg
    simpa only [d17396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15779 p = 1 := by simpa only [d17396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17755 p hg
    simpa only [d17396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17757 (p : Pattern) (guard : d17397 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17382 p = 1 := by simpa only [d17397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17749 p hg
    simpa only [d17397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17396 p = 1 := by simpa only [d17397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17756 p hg
    simpa only [d17397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17758 (p : Pattern) (guard : d17398 p = 1) : d48362 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17398, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16594 p hg
    simpa only [d17398, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17397 p = 1 := by simpa only [d17398, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17757 p hg
    simpa only [d17398, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17759 (p : Pattern) (guard : d17399 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17399, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16593 p hg
    simpa only [d17399, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17398 p = 1 := by simpa only [d17399, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17758 p hg
    simpa only [d17399, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17760 (p : Pattern) (guard : d6645 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17761 (p : Pattern) (guard : d6646 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d6645 p = 1 := by simpa only [d6646, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17760 p hg
    simpa only [d6646, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6646, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d6646, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17762 (p : Pattern) (guard : d6647 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d6646 p = 1 := by simpa only [d6647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17761 p hg
    simpa only [d6647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d6647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17763 (p : Pattern) (guard : d15792 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17764 (p : Pattern) (guard : d15793 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d15792 p = 1 := by simpa only [d15793, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17763 p hg
    simpa only [d15793, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15793, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d15793, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17765 (p : Pattern) (guard : d15794 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d15793 p = 1 := by simpa only [d15794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17764 p hg
    simpa only [d15794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d15794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d15794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17766 (p : Pattern) (guard : d15795 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d6647 p = 1 := by simpa only [d15795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17762 p hg
    simpa only [d15795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15794 p = 1 := by simpa only [d15795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17765 p hg
    simpa only [d15795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17767 (p : Pattern) (guard : d17400 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17396 p = 1 := by simpa only [d17400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17756 p hg
    simpa only [d17400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15795 p = 1 := by simpa only [d17400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17766 p hg
    simpa only [d17400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17768 (p : Pattern) (guard : d17401 p = 1) : d48362 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17401, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16594 p hg
    simpa only [d17401, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17400 p = 1 := by simpa only [d17401, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17767 p hg
    simpa only [d17401, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17769 (p : Pattern) (guard : d17402 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17402, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16593 p hg
    simpa only [d17402, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17401 p = 1 := by simpa only [d17402, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17768 p hg
    simpa only [d17402, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17770 (p : Pattern) (guard : d17403 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17399 p = 1 := by simpa only [d17403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17759 p hg
    simpa only [d17403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17402 p = 1 := by simpa only [d17403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17769 p hg
    simpa only [d17403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17771 (p : Pattern) (guard : d2348 p = 1) : d47799 p ≤ (0 : Int) + d47799 p := by
  omega
theorem compare17772 (p : Pattern) (guard : d2349 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2348 p = 1 := by simpa only [d2349, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17771 p hg
    simpa only [d2349, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2349, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16596 p hg
    simpa only [d2349, d48361, d48203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17773 (p : Pattern) (guard : d2355 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 159 with
  | false =>
    have hg : d2349 p = 1 := by simpa only [d2355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17772 p hg
    simpa only [d2355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16598 p hg
    simpa only [d2355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17774 (p : Pattern) (guard : d15813 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 158 with
  | false =>
    have hg : d2355 p = 1 := by simpa only [d15813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17773 p hg
    simpa only [d15813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15794 p = 1 := by simpa only [d15813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17765 p hg
    simpa only [d15813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17775 (p : Pattern) (guard : d17417 p = 1) : d48361 p ≤ (0 : Int) + d48203 p := by
  cases selected : p 157 with
  | false =>
    have hg : d17396 p = 1 := by simpa only [d17417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17756 p hg
    simpa only [d17417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d15813 p = 1 := by simpa only [d17417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17774 p hg
    simpa only [d17417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17776 (p : Pattern) (guard : d17418 p = 1) : d48362 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17418, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16594 p hg
    simpa only [d17418, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17417 p = 1 := by simpa only [d17418, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17775 p hg
    simpa only [d17418, d48362, d48204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17777 (p : Pattern) (guard : d17419 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17419, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16593 p hg
    simpa only [d17419, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17418 p = 1 := by simpa only [d17419, d48363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17776 p hg
    simpa only [d17419, d48363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17778 (p : Pattern) (guard : d17420 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 136 with
  | false =>
    have hg : d17419 p = 1 := by simpa only [d17420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17777 p hg
    simpa only [d17420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d17420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17779 (p : Pattern) (guard : d171214 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17403 p = 1 := by simpa only [d171214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17770 p hg
    simpa only [d171214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17420 p = 1 := by simpa only [d171214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17778 p hg
    simpa only [d171214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17780 (p : Pattern) (guard : d171215 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d171214 p = 1 := by simpa only [d171215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17779 p hg
    simpa only [d171215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d171215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17781 (p : Pattern) (guard : d171216 p = 1) : d48365 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d171215 p = 1 := by simpa only [d171216, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17780 p hg
    simpa only [d171216, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171216, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16608 p hg
    simpa only [d171216, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17782 (p : Pattern) (guard : d171217 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171217, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d171217, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171216 p = 1 := by simpa only [d171217, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17781 p hg
    simpa only [d171217, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17783 (p : Pattern) (guard : d17421 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 135 with
  | false =>
    have hg : d17420 p = 1 := by simpa only [d17421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17778 p hg
    simpa only [d17421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d17421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17784 (p : Pattern) (guard : d17422 p = 1) : d48363 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 119 with
  | false =>
    have hg : d17421 p = 1 := by simpa only [d17422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17783 p hg
    simpa only [d17422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16604 p hg
    simpa only [d17422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17785 (p : Pattern) (guard : d17423 p = 1) : d48365 p ≤ (0 : Int) + d48204 p := by
  cases selected : p 116 with
  | false =>
    have hg : d17422 p = 1 := by simpa only [d17423, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17784 p hg
    simpa only [d17423, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17423, d48365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16608 p hg
    simpa only [d17423, d48365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17786 (p : Pattern) (guard : d17424 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d17424, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16497 p hg
    simpa only [d17424, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17423 p = 1 := by simpa only [d17424, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17785 p hg
    simpa only [d17424, d48366, d171290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17787 (p : Pattern) (guard : d171218 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d171217 p = 1 := by simpa only [d171218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17782 p hg
    simpa only [d171218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17424 p = 1 := by simpa only [d171218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17786 p hg
    simpa only [d171218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17788 (p : Pattern) (guard : d171219 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d171218 p = 1 := by simpa only [d171219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17787 p hg
    simpa only [d171219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17789 (p : Pattern) (guard : d171220 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d171219 p = 1 := by simpa only [d171220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17788 p hg
    simpa only [d171220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17790 (p : Pattern) (guard : d171221 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d171220 p = 1 := by simpa only [d171221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17789 p hg
    simpa only [d171221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17791 (p : Pattern) (guard : d17491 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 113 with
  | false =>
    have hg : d17424 p = 1 := by simpa only [d17491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17786 p hg
    simpa only [d17491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d17491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17792 (p : Pattern) (guard : d17492 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 96 with
  | false =>
    have hg : d17491 p = 1 := by simpa only [d17492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17791 p hg
    simpa only [d17492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d17492, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17793 (p : Pattern) (guard : d17493 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 95 with
  | false =>
    have hg : d17492 p = 1 := by simpa only [d17493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17792 p hg
    simpa only [d17493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d17493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17794 (p : Pattern) (guard : d17494 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 93 with
  | false =>
    have hg : d17493 p = 1 := by simpa only [d17494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17793 p hg
    simpa only [d17494, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17494, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d17494, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17795 (p : Pattern) (guard : d171222 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 91 with
  | false =>
    have hg : d171221 p = 1 := by simpa only [d171222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17790 p hg
    simpa only [d171222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17494 p = 1 := by simpa only [d171222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17794 p hg
    simpa only [d171222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17796 (p : Pattern) (guard : d171223 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171222 p = 1 := by simpa only [d171223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17795 p hg
    simpa only [d171223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17797 (p : Pattern) (guard : d171224 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 89 with
  | false =>
    have hg : d171223 p = 1 := by simpa only [d171224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17796 p hg
    simpa only [d171224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17798 (p : Pattern) (guard : d171225 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171224 p = 1 := by simpa only [d171225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17797 p hg
    simpa only [d171225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17799 (p : Pattern) (guard : d171226 p = 1) : d48366 p ≤ (0 : Int) + d171290 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16592 p hg
    simpa only [d171226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171225 p = 1 := by simpa only [d171226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17798 p hg
    simpa only [d171226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17800 (p : Pattern) (guard : d171227 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171227, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16495 p hg
    simpa only [d171227, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171226 p = 1 := by simpa only [d171227, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17799 p hg
    simpa only [d171227, d48367, d171291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17801 (p : Pattern) (guard : d171228 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171227 p = 1 := by simpa only [d171228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17800 p hg
    simpa only [d171228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17802 (p : Pattern) (guard : d171229 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 69 with
  | false =>
    have hg : d171228 p = 1 := by simpa only [d171229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17801 p hg
    simpa only [d171229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17803 (p : Pattern) (guard : d171230 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 51 with
  | false =>
    have hg : d171229 p = 1 := by simpa only [d171230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17802 p hg
    simpa only [d171230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17804 (p : Pattern) (guard : d171231 p = 1) : d48367 p ≤ (0 : Int) + d171291 p := by
  cases selected : p 50 with
  | false =>
    have hg : d171230 p = 1 := by simpa only [d171231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17803 p hg
    simpa only [d171231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16591 p hg
    simpa only [d171231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17805 (p : Pattern) (guard : d171232 p = 1) : d48387 p ≤ (0 : Int) + d171294 p := by
  cases selected : p 49 with
  | false =>
    have hg : d171231 p = 1 := by simpa only [d171232, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17804 p hg
    simpa only [d171232, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171232, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16625 p hg
    simpa only [d171232, d48387, d171294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17806 (p : Pattern) (guard : d171233 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 48 with
  | false =>
    have hg : d171213 p = 1 := by simpa only [d171233, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17738 p hg
    simpa only [d171233, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171232 p = 1 := by simpa only [d171233, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17805 p hg
    simpa only [d171233, d48388, d171295, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17807 (p : Pattern) (guard : d171234 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171233 p = 1 := by simpa only [d171234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d171234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17808 (p : Pattern) (guard : d171235 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171234 p = 1 := by simpa only [d171235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17807 p hg
    simpa only [d171235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17809 (p : Pattern) (guard : d171236 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171235 p = 1 := by simpa only [d171236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17808 p hg
    simpa only [d171236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17810 (p : Pattern) (guard : d171237 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171236 p = 1 := by simpa only [d171237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17809 p hg
    simpa only [d171237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17811 (p : Pattern) (guard : d171238 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171237 p = 1 := by simpa only [d171238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d171238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17812 (p : Pattern) (guard : d171239 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171238 p = 1 := by simpa only [d171239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17811 p hg
    simpa only [d171239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17813 (p : Pattern) (guard : d171240 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171239 p = 1 := by simpa only [d171240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17812 p hg
    simpa only [d171240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17814 (p : Pattern) (guard : d171241 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171240 p = 1 := by simpa only [d171241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17813 p hg
    simpa only [d171241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17815 (p : Pattern) (guard : d171242 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171241 p = 1 := by simpa only [d171242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17814 p hg
    simpa only [d171242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17816 (p : Pattern) (guard : d171243 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d171243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171242 p = 1 := by simpa only [d171243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17815 p hg
    simpa only [d171243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17817 (p : Pattern) (guard : d171244 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d171205 p = 1 := by simpa only [d171244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17571 p hg
    simpa only [d171244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d171243 p = 1 := by simpa only [d171244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17816 p hg
    simpa only [d171244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17818 (p : Pattern) (guard : d171245 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 260 with
  | false =>
    have hg : d171244 p = 1 := by simpa only [d171245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17817 p hg
    simpa only [d171245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17819 (p : Pattern) (guard : d171246 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 259 with
  | false =>
    have hg : d171245 p = 1 := by simpa only [d171246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17818 p hg
    simpa only [d171246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17820 (p : Pattern) (guard : d171247 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 258 with
  | false =>
    have hg : d171246 p = 1 := by simpa only [d171247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17819 p hg
    simpa only [d171247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17821 (p : Pattern) (guard : d171248 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 257 with
  | false =>
    have hg : d171247 p = 1 := by simpa only [d171248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17820 p hg
    simpa only [d171248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17822 (p : Pattern) (guard : d171249 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 256 with
  | false =>
    have hg : d171248 p = 1 := by simpa only [d171249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17821 p hg
    simpa only [d171249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17823 (p : Pattern) (guard : d171250 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 255 with
  | false =>
    have hg : d171249 p = 1 := by simpa only [d171250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17822 p hg
    simpa only [d171250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17824 (p : Pattern) (guard : d171251 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 254 with
  | false =>
    have hg : d171250 p = 1 := by simpa only [d171251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17823 p hg
    simpa only [d171251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17825 (p : Pattern) (guard : d171252 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 253 with
  | false =>
    have hg : d171251 p = 1 := by simpa only [d171252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17824 p hg
    simpa only [d171252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17826 (p : Pattern) (guard : d171253 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 252 with
  | false =>
    have hg : d171252 p = 1 := by simpa only [d171253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17825 p hg
    simpa only [d171253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17827 (p : Pattern) (guard : d171254 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 251 with
  | false =>
    have hg : d171253 p = 1 := by simpa only [d171254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17826 p hg
    simpa only [d171254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17828 (p : Pattern) (guard : d171255 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 250 with
  | false =>
    have hg : d171254 p = 1 := by simpa only [d171255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17827 p hg
    simpa only [d171255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17829 (p : Pattern) (guard : d171256 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 249 with
  | false =>
    have hg : d171255 p = 1 := by simpa only [d171256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17828 p hg
    simpa only [d171256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17830 (p : Pattern) (guard : d171257 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 245 with
  | false =>
    have hg : d171256 p = 1 := by simpa only [d171257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17829 p hg
    simpa only [d171257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17831 (p : Pattern) (guard : d171258 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 200 with
  | false =>
    have hg : d171257 p = 1 := by simpa only [d171258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17830 p hg
    simpa only [d171258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17832 (p : Pattern) (guard : d171259 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 199 with
  | false =>
    have hg : d171258 p = 1 := by simpa only [d171259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17831 p hg
    simpa only [d171259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17833 (p : Pattern) (guard : d171260 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 186 with
  | false =>
    have hg : d171259 p = 1 := by simpa only [d171260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17832 p hg
    simpa only [d171260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17834 (p : Pattern) (guard : d171261 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 185 with
  | false =>
    have hg : d171260 p = 1 := by simpa only [d171261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17833 p hg
    simpa only [d171261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17835 (p : Pattern) (guard : d171262 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 184 with
  | false =>
    have hg : d171261 p = 1 := by simpa only [d171262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17834 p hg
    simpa only [d171262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17836 (p : Pattern) (guard : d171263 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 181 with
  | false =>
    have hg : d171262 p = 1 := by simpa only [d171263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17835 p hg
    simpa only [d171263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17837 (p : Pattern) (guard : d171264 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 177 with
  | false =>
    have hg : d171263 p = 1 := by simpa only [d171264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17836 p hg
    simpa only [d171264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17838 (p : Pattern) (guard : d171265 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 164 with
  | false =>
    have hg : d171264 p = 1 := by simpa only [d171265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17837 p hg
    simpa only [d171265, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171265, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171265, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17839 (p : Pattern) (guard : d171266 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 156 with
  | false =>
    have hg : d171265 p = 1 := by simpa only [d171266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17838 p hg
    simpa only [d171266, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171266, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171266, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17840 (p : Pattern) (guard : d171267 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 155 with
  | false =>
    have hg : d171266 p = 1 := by simpa only [d171267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17839 p hg
    simpa only [d171267, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171267, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171267, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17841 (p : Pattern) (guard : d171268 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 134 with
  | false =>
    have hg : d171267 p = 1 := by simpa only [d171268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17840 p hg
    simpa only [d171268, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171268, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171268, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17842 (p : Pattern) (guard : d171269 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 133 with
  | false =>
    have hg : d171268 p = 1 := by simpa only [d171269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17841 p hg
    simpa only [d171269, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171269, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171269, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17843 (p : Pattern) (guard : d171270 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 120 with
  | false =>
    have hg : d171269 p = 1 := by simpa only [d171270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17842 p hg
    simpa only [d171270, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171270, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171270, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17844 (p : Pattern) (guard : d171271 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 118 with
  | false =>
    have hg : d171270 p = 1 := by simpa only [d171271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17843 p hg
    simpa only [d171271, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171271, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171271, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17845 (p : Pattern) (guard : d171272 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 114 with
  | false =>
    have hg : d171271 p = 1 := by simpa only [d171272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17844 p hg
    simpa only [d171272, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171272, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171272, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17846 (p : Pattern) (guard : d171273 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 111 with
  | false =>
    have hg : d171272 p = 1 := by simpa only [d171273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17845 p hg
    simpa only [d171273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17847 (p : Pattern) (guard : d171274 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 98 with
  | false =>
    have hg : d171273 p = 1 := by simpa only [d171274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17846 p hg
    simpa only [d171274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17848 (p : Pattern) (guard : d171275 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 97 with
  | false =>
    have hg : d171274 p = 1 := by simpa only [d171275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17847 p hg
    simpa only [d171275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17849 (p : Pattern) (guard : d171276 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 94 with
  | false =>
    have hg : d171275 p = 1 := by simpa only [d171276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17848 p hg
    simpa only [d171276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17850 (p : Pattern) (guard : d171277 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 76 with
  | false =>
    have hg : d171276 p = 1 := by simpa only [d171277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17849 p hg
    simpa only [d171277, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171277, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171277, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17851 (p : Pattern) (guard : d171278 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 67 with
  | false =>
    have hg : d171277 p = 1 := by simpa only [d171278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17850 p hg
    simpa only [d171278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17852 (p : Pattern) (guard : d171279 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 52 with
  | false =>
    have hg : d171278 p = 1 := by simpa only [d171279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17851 p hg
    simpa only [d171279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17853 (p : Pattern) (guard : d171280 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 47 with
  | false =>
    have hg : d171279 p = 1 := by simpa only [d171280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17852 p hg
    simpa only [d171280, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171280, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171280, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17854 (p : Pattern) (guard : d171281 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 46 with
  | false =>
    have hg : d171280 p = 1 := by simpa only [d171281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17853 p hg
    simpa only [d171281, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171281, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171281, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17855 (p : Pattern) (guard : d171282 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 45 with
  | false =>
    have hg : d171281 p = 1 := by simpa only [d171282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17854 p hg
    simpa only [d171282, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171282, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171282, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17856 (p : Pattern) (guard : d171283 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 30 with
  | false =>
    have hg : d171282 p = 1 := by simpa only [d171283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17855 p hg
    simpa only [d171283, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171283, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171283, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17857 (p : Pattern) (guard : d171284 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 29 with
  | false =>
    have hg : d171283 p = 1 := by simpa only [d171284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17856 p hg
    simpa only [d171284, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171284, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171284, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17858 (p : Pattern) (guard : d171285 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 28 with
  | false =>
    have hg : d171284 p = 1 := by simpa only [d171285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17857 p hg
    simpa only [d171285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17859 (p : Pattern) (guard : d171286 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 27 with
  | false =>
    have hg : d171285 p = 1 := by simpa only [d171286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17858 p hg
    simpa only [d171286, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171286, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171286, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17860 (p : Pattern) (guard : d171287 p = 1) : d48388 p ≤ (0 : Int) + d171295 p := by
  cases selected : p 25 with
  | false =>
    have hg : d171286 p = 1 := by simpa only [d171287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17859 p hg
    simpa only [d171287, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d171287, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare16493 p hg
    simpa only [d171287, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17861 (p : Pattern) (guard : d0 p = 1) : d48388 p ≤ (-1 : Int) + d49280 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17862 (p : Pattern) (guard : d0 p = 1) : d48388 p ≤ (-2 : Int) + d49280 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17863 (p : Pattern) (guard : d0 p = 1) : d48388 p ≤ (-1 : Int) + d171439 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17864 (p : Pattern) (guard : d0 p = 1) : d48388 p ≤ (-2 : Int) + d171439 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17865 (p : Pattern) (guard : d0 p = 1) : d48388 p ≤ (-1 : Int) + d48547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17866 (p : Pattern) (guard : d0 p = 1) : d48388 p ≤ (-2 : Int) + d48547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17867 (p : Pattern) (guard : d0 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17868 (p : Pattern) (guard : d0 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17869 (p : Pattern) (guard : d0 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17870 (p : Pattern) (guard : d0 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17871 (p : Pattern) (guard : d0 p = 1) : d48336 p ≤ (1 : Int) + d173714 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17872 (p : Pattern) (guard : d0 p = 1) : d48317 p ≤ (1 : Int) + d173707 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17873 (p : Pattern) (guard : d0 p = 1) : d48325 p ≤ (1 : Int) + d173705 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17874 (p : Pattern) (guard : d0 p = 1) : d47655 p ≤ (1 : Int) + d47654 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17875 (p : Pattern) (guard : d24 p = 1) : d47619 p ≤ (1 : Int) + d47619 p := by
  omega
theorem compare17876 (p : Pattern) (guard : d0 p = 1) : d47659 p ≤ (1 : Int) + d47625 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17877 (p : Pattern) (guard : d25 p = 1) : d47660 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17875 p hg
    simpa only [d25, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17876 p hg
    simpa only [d25, d47660, d47654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17878 (p : Pattern) (guard : d0 p = 1) : d47662 p ≤ (1 : Int) + d47654 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17879 (p : Pattern) (guard : d26 p = 1) : d47663 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 162 with
  | false =>
    have hg : d25 p = 1 := by simpa only [d26, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17877 p hg
    simpa only [d26, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d26, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17878 p hg
    simpa only [d26, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17880 (p : Pattern) (guard : d27 p = 1) : d47664 p ≤ (1 : Int) + d47654 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17874 p hg
    simpa only [d27, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17879 p hg
    simpa only [d27, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17881 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d48408 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17882 (p : Pattern) (guard : d28 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17880 p hg
    simpa only [d28, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17881 p hg
    simpa only [d28, d48313, d173708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17883 (p : Pattern) (guard : d0 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17884 (p : Pattern) (guard : d29 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17882 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17885 (p : Pattern) (guard : d30 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17884 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17886 (p : Pattern) (guard : d31 p = 1) : d48313 p ≤ (1 : Int) + d173708 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17885 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17883 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17887 (p : Pattern) (guard : d32 p = 1) : d48326 p ≤ (1 : Int) + d173709 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17873 p hg
    simpa only [d32, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31 p = 1 := by simpa only [d32, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17886 p hg
    simpa only [d32, d48326, d173709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17888 (p : Pattern) (guard : d33 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17872 p hg
    simpa only [d33, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17887 p hg
    simpa only [d33, d48337, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17889 (p : Pattern) (guard : d0 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17890 (p : Pattern) (guard : d34 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17888 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17891 (p : Pattern) (guard : d35 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17890 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17892 (p : Pattern) (guard : d36 p = 1) : d48337 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17891 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17889 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17893 (p : Pattern) (guard : d0 p = 1) : d48328 p ≤ (1 : Int) + d173715 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17894 (p : Pattern) (guard : d37 p = 1) : d48338 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17892 p hg
    simpa only [d37, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d37, d48338, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17895 (p : Pattern) (guard : d38 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17871 p hg
    simpa only [d38, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17894 p hg
    simpa only [d38, d48339, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17896 (p : Pattern) (guard : d39 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17895 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17897 (p : Pattern) (guard : d40 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17896 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17898 (p : Pattern) (guard : d41 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17897 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17899 (p : Pattern) (guard : d42 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d41 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17898 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17900 (p : Pattern) (guard : d43 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d42 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17899 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17901 (p : Pattern) (guard : d44 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d43 p = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17900 p hg
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17902 (p : Pattern) (guard : d45 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d44 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17901 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17903 (p : Pattern) (guard : d46 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17902 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17904 (p : Pattern) (guard : d47 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17903 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17905 (p : Pattern) (guard : d48 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d48, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d48, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47 p = 1 := by simpa only [d48, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17904 p hg
    simpa only [d48, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17906 (p : Pattern) (guard : d0 p = 1) : d48321 p ≤ (1 : Int) + d173714 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17907 (p : Pattern) (guard : d0 p = 1) : d48324 p ≤ (1 : Int) + d173707 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17908 (p : Pattern) (guard : d33 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17907 p hg
    simpa only [d33, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17887 p hg
    simpa only [d33, d48327, d173710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17909 (p : Pattern) (guard : d0 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17910 (p : Pattern) (guard : d34 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17908 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17911 (p : Pattern) (guard : d35 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17910 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17912 (p : Pattern) (guard : d36 p = 1) : d48327 p ≤ (1 : Int) + d173710 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17911 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17909 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17913 (p : Pattern) (guard : d37 p = 1) : d48329 p ≤ (1 : Int) + d173716 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17912 p hg
    simpa only [d37, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17893 p hg
    simpa only [d37, d48329, d173716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17914 (p : Pattern) (guard : d38 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17906 p hg
    simpa only [d38, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17913 p hg
    simpa only [d38, d48330, d173717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17915 (p : Pattern) (guard : d39 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17914 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17916 (p : Pattern) (guard : d40 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17915 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17917 (p : Pattern) (guard : d41 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17916 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17918 (p : Pattern) (guard : d42 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d41 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17917 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17919 (p : Pattern) (guard : d43 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d42 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17918 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17920 (p : Pattern) (guard : d44 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d43 p = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17919 p hg
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17921 (p : Pattern) (guard : d45 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d44 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17920 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17922 (p : Pattern) (guard : d46 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17921 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17923 (p : Pattern) (guard : d47 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17922 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17924 (p : Pattern) (guard : d49 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 93 with
  | false =>
    have hg : d41 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17898 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17925 (p : Pattern) (guard : d50 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 91 with
  | false =>
    have hg : d49 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17924 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17926 (p : Pattern) (guard : d51 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d50 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17925 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17927 (p : Pattern) (guard : d52 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d51 p = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17926 p hg
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17928 (p : Pattern) (guard : d53 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d52 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17927 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17929 (p : Pattern) (guard : d54 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17928 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17930 (p : Pattern) (guard : d55 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d47 p = 1 := by simpa only [d55, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17923 p hg
    simpa only [d55, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54 p = 1 := by simpa only [d55, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17929 p hg
    simpa only [d55, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17931 (p : Pattern) (guard : d56 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d48 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17905 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17930 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17932 (p : Pattern) (guard : d57 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d56 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17931 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17933 (p : Pattern) (guard : d58 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 51 with
  | false =>
    have hg : d57 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17932 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17934 (p : Pattern) (guard : d59 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d58 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17933 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17935 (p : Pattern) (guard : d0 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17936 (p : Pattern) (guard : d0 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17937 (p : Pattern) (guard : d0 p = 1) : d48351 p ≤ (1 : Int) + d173725 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17938 (p : Pattern) (guard : d0 p = 1) : d48353 p ≤ (1 : Int) + d173720 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17939 (p : Pattern) (guard : d0 p = 1) : d48344 p ≤ (1 : Int) + d173718 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17940 (p : Pattern) (guard : d0 p = 1) : d47734 p ≤ (1 : Int) + d47733 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17941 (p : Pattern) (guard : d24 p = 1) : d47708 p ≤ (1 : Int) + d47708 p := by
  omega
theorem compare17942 (p : Pattern) (guard : d0 p = 1) : d47661 p ≤ (1 : Int) + d47659 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17943 (p : Pattern) (guard : d25 p = 1) : d47735 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d24 p = 1 := by simpa only [d25, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17941 p hg
    simpa only [d25, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d25, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17942 p hg
    simpa only [d25, d47735, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17944 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d47733 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17945 (p : Pattern) (guard : d26 p = 1) : d47736 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 162 with
  | false =>
    have hg : d25 p = 1 := by simpa only [d26, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17943 p hg
    simpa only [d26, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d26, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17944 p hg
    simpa only [d26, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17946 (p : Pattern) (guard : d27 p = 1) : d47737 p ≤ (1 : Int) + d47733 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17940 p hg
    simpa only [d27, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17945 p hg
    simpa only [d27, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17947 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d47752 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17948 (p : Pattern) (guard : d28 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17946 p hg
    simpa only [d28, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17947 p hg
    simpa only [d28, d48345, d173721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17949 (p : Pattern) (guard : d0 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17950 (p : Pattern) (guard : d29 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17948 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17951 (p : Pattern) (guard : d30 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17950 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17952 (p : Pattern) (guard : d31 p = 1) : d48345 p ≤ (1 : Int) + d173721 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17951 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17949 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17953 (p : Pattern) (guard : d32 p = 1) : d48346 p ≤ (1 : Int) + d173722 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17939 p hg
    simpa only [d32, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31 p = 1 := by simpa only [d32, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17952 p hg
    simpa only [d32, d48346, d173722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17954 (p : Pattern) (guard : d33 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17938 p hg
    simpa only [d33, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17953 p hg
    simpa only [d33, d48354, d173723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17955 (p : Pattern) (guard : d0 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17956 (p : Pattern) (guard : d34 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17954 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17957 (p : Pattern) (guard : d35 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17956 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17958 (p : Pattern) (guard : d36 p = 1) : d48354 p ≤ (1 : Int) + d173723 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17957 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17955 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17959 (p : Pattern) (guard : d0 p = 1) : d48355 p ≤ (1 : Int) + d173724 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17960 (p : Pattern) (guard : d37 p = 1) : d48356 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17958 p hg
    simpa only [d37, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17959 p hg
    simpa only [d37, d48356, d173725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17961 (p : Pattern) (guard : d38 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17937 p hg
    simpa only [d38, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17960 p hg
    simpa only [d38, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17962 (p : Pattern) (guard : d39 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17961 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17963 (p : Pattern) (guard : d40 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17962 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17964 (p : Pattern) (guard : d41 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17963 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17965 (p : Pattern) (guard : d49 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 93 with
  | false =>
    have hg : d41 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17964 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17966 (p : Pattern) (guard : d50 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 91 with
  | false =>
    have hg : d49 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17965 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17967 (p : Pattern) (guard : d51 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 90 with
  | false =>
    have hg : d50 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17966 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17968 (p : Pattern) (guard : d52 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 89 with
  | false =>
    have hg : d51 p = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17967 p hg
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17969 (p : Pattern) (guard : d53 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d52 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17968 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17970 (p : Pattern) (guard : d54 p = 1) : d48357 p ≤ (1 : Int) + d173725 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17936 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17969 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17971 (p : Pattern) (guard : d60 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d60, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54 p = 1 := by simpa only [d60, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17970 p hg
    simpa only [d60, d48358, d173726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17972 (p : Pattern) (guard : d61 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60 p = 1 := by simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17971 p hg
    simpa only [d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17973 (p : Pattern) (guard : d62 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 69 with
  | false =>
    have hg : d61 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17972 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17974 (p : Pattern) (guard : d63 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 51 with
  | false =>
    have hg : d62 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17973 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17975 (p : Pattern) (guard : d64 p = 1) : d48358 p ≤ (1 : Int) + d173726 p := by
  cases selected : p 50 with
  | false =>
    have hg : d63 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17974 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17935 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17976 (p : Pattern) (guard : d65 p = 1) : d48359 p ≤ (1 : Int) + d173727 p := by
  cases selected : p 49 with
  | false =>
    have hg : d59 p = 1 := by simpa only [d65, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17934 p hg
    simpa only [d65, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d64 p = 1 := by simpa only [d65, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17975 p hg
    simpa only [d65, d48359, d173727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17977 (p : Pattern) (guard : d0 p = 1) : d48387 p ≤ (1 : Int) + d173754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17978 (p : Pattern) (guard : d2672 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 48 with
  | false =>
    have hg : d65 p = 1 := by simpa only [d2672, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17976 p hg
    simpa only [d2672, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2672, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17977 p hg
    simpa only [d2672, d48388, d173755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17979 (p : Pattern) (guard : d2673 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d2673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2672 p = 1 := by simpa only [d2673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17978 p hg
    simpa only [d2673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17980 (p : Pattern) (guard : d2674 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d2674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2673 p = 1 := by simpa only [d2674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17979 p hg
    simpa only [d2674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17981 (p : Pattern) (guard : d2675 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2674 p = 1 := by simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17980 p hg
    simpa only [d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17982 (p : Pattern) (guard : d2676 p = 1) : d48388 p ≤ (1 : Int) + d173755 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17867 p hg
    simpa only [d2676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2675 p = 1 := by simpa only [d2676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17981 p hg
    simpa only [d2676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17983 (p : Pattern) (guard : d100 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17900 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17984 (p : Pattern) (guard : d101 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d100 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17983 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17985 (p : Pattern) (guard : d102 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17984 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17986 (p : Pattern) (guard : d103 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17985 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17987 (p : Pattern) (guard : d104 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d104, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d104, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d103 p = 1 := by simpa only [d104, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17986 p hg
    simpa only [d104, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17988 (p : Pattern) (guard : d105 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d104 p = 1 := by simpa only [d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17987 p hg
    simpa only [d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17989 (p : Pattern) (guard : d106 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 69 with
  | false =>
    have hg : d105 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17988 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17868 p hg
    simpa only [d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17990 (p : Pattern) (guard : d100 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d43 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17919 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17991 (p : Pattern) (guard : d101 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d100 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17990 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17992 (p : Pattern) (guard : d102 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d101 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17991 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17993 (p : Pattern) (guard : d103 p = 1) : d48330 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17869 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d102 p = 1 := by simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17992 p hg
    simpa only [d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17994 (p : Pattern) (guard : d107 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d50 p = 1 := by simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17925 p hg
    simpa only [d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17995 (p : Pattern) (guard : d108 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 89 with
  | false =>
    have hg : d107 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17994 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17996 (p : Pattern) (guard : d109 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d108 p = 1 := by simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17995 p hg
    simpa only [d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17997 (p : Pattern) (guard : d110 p = 1) : d48339 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17870 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d109 p = 1 := by simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17996 p hg
    simpa only [d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17998 (p : Pattern) (guard : d111 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 71 with
  | false =>
    have hg : d103 p = 1 := by simpa only [d111, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17993 p hg
    simpa only [d111, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d110 p = 1 := by simpa only [d111, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17997 p hg
    simpa only [d111, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17999 (p : Pattern) (guard : d112 p = 1) : d48340 p ≤ (1 : Int) + d173717 p := by
  cases selected : p 70 with
  | false =>
    have hg : d104 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17987 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d111 p = 1 := by simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17998 p hg
    simpa only [d112, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
