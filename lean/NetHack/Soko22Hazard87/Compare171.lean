import NetHack.Soko22Hazard87.Compare170
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare42750 (p : Pattern) (guard : d349171 p = 1) : d51039 p ≤ (0 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d349165 p = 1 := by simpa only [d349171, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42693 p hg
    simpa only [d349171, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349170 p = 1 := by simpa only [d349171, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42749 p hg
    simpa only [d349171, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42751 (p : Pattern) (guard : d308 p = 1) : d2 p ≤ (0 : Int) + d2 p := by
  omega
theorem compare42752 (p : Pattern) (guard : d1519 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42751 p hg
    simpa only [d1519, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42512 p hg
    simpa only [d1519, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42753 (p : Pattern) (guard : d1531 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42752 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42754 (p : Pattern) (guard : d1547 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42753 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42755 (p : Pattern) (guard : d39244 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42754 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42756 (p : Pattern) (guard : d337457 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d39244 p = 1 := by simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42755 p hg
    simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42757 (p : Pattern) (guard : d337458 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d337457 p = 1 := by simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42756 p hg
    simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42758 (p : Pattern) (guard : d337473 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d337458 p = 1 := by simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42757 p hg
    simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42759 (p : Pattern) (guard : d258107 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d39244 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42755 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42760 (p : Pattern) (guard : d258108 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258107 p = 1 := by simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42759 p hg
    simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42761 (p : Pattern) (guard : d258109 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258108 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42760 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42510 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42762 (p : Pattern) (guard : d348629 p = 1) : d50849 p ≤ (0 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d337473 p = 1 := by simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42758 p hg
    simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42761 p hg
    simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42763 (p : Pattern) (guard : d348630 p = 1) : d50874 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d348629 p = 1 := by simpa only [d348630, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42762 p hg
    simpa only [d348630, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348630, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42524 p hg
    simpa only [d348630, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42764 (p : Pattern) (guard : d348631 p = 1) : d50874 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d348630 p = 1 := by simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42763 p hg
    simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42509 p hg
    simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42765 (p : Pattern) (guard : d348776 p = 1) : d50874 p ≤ (0 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42509 p hg
    simpa only [d348776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348631 p = 1 := by simpa only [d348776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42764 p hg
    simpa only [d348776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42766 (p : Pattern) (guard : d348632 p = 1) : d51067 p ≤ (0 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348631 p = 1 := by simpa only [d348632, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42618 p hg
    simpa only [d348632, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348632, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42457 p hg
    simpa only [d348632, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42767 (p : Pattern) (guard : d348777 p = 1) : d51068 p ≤ (0 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348776 p = 1 := by simpa only [d348777, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42765 p hg
    simpa only [d348777, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348632 p = 1 := by simpa only [d348777, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42766 p hg
    simpa only [d348777, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42768 (p : Pattern) (guard : d308 p = 1) : d6 p ≤ (0 : Int) + d6 p := by
  omega
theorem compare42769 (p : Pattern) (guard : d1519 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42768 p hg
    simpa only [d1519, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42532 p hg
    simpa only [d1519, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42770 (p : Pattern) (guard : d1531 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42769 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42771 (p : Pattern) (guard : d1547 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42770 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42772 (p : Pattern) (guard : d39244 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42771 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42773 (p : Pattern) (guard : d337457 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d39244 p = 1 := by simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42772 p hg
    simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42774 (p : Pattern) (guard : d337458 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d337457 p = 1 := by simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42773 p hg
    simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42775 (p : Pattern) (guard : d337473 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d337458 p = 1 := by simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42774 p hg
    simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42776 (p : Pattern) (guard : d258107 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d39244 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42772 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42777 (p : Pattern) (guard : d258108 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258107 p = 1 := by simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42776 p hg
    simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42778 (p : Pattern) (guard : d258109 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258108 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42777 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42530 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42779 (p : Pattern) (guard : d348629 p = 1) : d50852 p ≤ (0 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d337473 p = 1 := by simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42775 p hg
    simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42778 p hg
    simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42780 (p : Pattern) (guard : d348630 p = 1) : d50900 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d348629 p = 1 := by simpa only [d348630, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42779 p hg
    simpa only [d348630, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348630, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42544 p hg
    simpa only [d348630, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42781 (p : Pattern) (guard : d348631 p = 1) : d50900 p ≤ (0 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d348630 p = 1 := by simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42780 p hg
    simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42546 p hg
    simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42782 (p : Pattern) (guard : d348632 p = 1) : d50908 p ≤ (0 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348631 p = 1 := by simpa only [d348632, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42781 p hg
    simpa only [d348632, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348632, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d348632, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42783 (p : Pattern) (guard : d348633 p = 1) : d50909 p ≤ (0 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348632 p = 1 := by simpa only [d348633, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42782 p hg
    simpa only [d348633, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348633, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d348633, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42784 (p : Pattern) (guard : d348778 p = 1) : d51069 p ≤ (0 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d348777 p = 1 := by simpa only [d348778, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42767 p hg
    simpa only [d348778, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348633 p = 1 := by simpa only [d348778, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42783 p hg
    simpa only [d348778, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42785 (p : Pattern) (guard : d348779 p = 1) : d51073 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d348778 p = 1 := by simpa only [d348779, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42784 p hg
    simpa only [d348779, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348779, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42551 p hg
    simpa only [d348779, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42786 (p : Pattern) (guard : d348780 p = 1) : d51073 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42508 p hg
    simpa only [d348780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348779 p = 1 := by simpa only [d348780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42785 p hg
    simpa only [d348780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42787 (p : Pattern) (guard : d348781 p = 1) : d51073 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42508 p hg
    simpa only [d348781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348780 p = 1 := by simpa only [d348781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42786 p hg
    simpa only [d348781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42788 (p : Pattern) (guard : d348785 p = 1) : d51073 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d348779 p = 1 := by simpa only [d348785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42785 p hg
    simpa only [d348785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42508 p hg
    simpa only [d348785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42789 (p : Pattern) (guard : d348791 p = 1) : d51073 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42508 p hg
    simpa only [d348791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348785 p = 1 := by simpa only [d348791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42788 p hg
    simpa only [d348791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42790 (p : Pattern) (guard : d348792 p = 1) : d51073 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348781 p = 1 := by simpa only [d348792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42787 p hg
    simpa only [d348792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348791 p = 1 := by simpa only [d348792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42789 p hg
    simpa only [d348792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42791 (p : Pattern) (guard : d348793 p = 1) : d51074 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348793, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42507 p hg
    simpa only [d348793, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348792 p = 1 := by simpa only [d348793, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42790 p hg
    simpa only [d348793, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42792 (p : Pattern) (guard : d348794 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348794, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42506 p hg
    simpa only [d348794, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348793 p = 1 := by simpa only [d348794, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42791 p hg
    simpa only [d348794, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42793 (p : Pattern) (guard : d348795 p = 1) : d51073 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348791 p = 1 := by simpa only [d348795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42789 p hg
    simpa only [d348795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42508 p hg
    simpa only [d348795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42794 (p : Pattern) (guard : d348796 p = 1) : d51074 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348796, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42507 p hg
    simpa only [d348796, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348795 p = 1 := by simpa only [d348796, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42793 p hg
    simpa only [d348796, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42795 (p : Pattern) (guard : d348797 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348797, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42506 p hg
    simpa only [d348797, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348796 p = 1 := by simpa only [d348797, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42794 p hg
    simpa only [d348797, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42796 (p : Pattern) (guard : d348798 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348794 p = 1 := by simpa only [d348798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42792 p hg
    simpa only [d348798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348797 p = 1 := by simpa only [d348798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42795 p hg
    simpa only [d348798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42797 (p : Pattern) (guard : d348803 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348797 p = 1 := by simpa only [d348803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42795 p hg
    simpa only [d348803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42564 p hg
    simpa only [d348803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42798 (p : Pattern) (guard : d348804 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348798 p = 1 := by simpa only [d348804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42796 p hg
    simpa only [d348804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348803 p = 1 := by simpa only [d348804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42797 p hg
    simpa only [d348804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42799 (p : Pattern) (guard : d348805 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348804 p = 1 := by simpa only [d348805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42798 p hg
    simpa only [d348805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42564 p hg
    simpa only [d348805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42800 (p : Pattern) (guard : d348806 p = 1) : d51077 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348805 p = 1 := by simpa only [d348806, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42799 p hg
    simpa only [d348806, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348806, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42568 p hg
    simpa only [d348806, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42801 (p : Pattern) (guard : d348807 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348807, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42326 p hg
    simpa only [d348807, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348806 p = 1 := by simpa only [d348807, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42800 p hg
    simpa only [d348807, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42802 (p : Pattern) (guard : d348812 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348803 p = 1 := by simpa only [d348812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42797 p hg
    simpa only [d348812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42564 p hg
    simpa only [d348812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42803 (p : Pattern) (guard : d348813 p = 1) : d51075 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348812 p = 1 := by simpa only [d348813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42802 p hg
    simpa only [d348813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42564 p hg
    simpa only [d348813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42804 (p : Pattern) (guard : d348814 p = 1) : d51077 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348813 p = 1 := by simpa only [d348814, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42803 p hg
    simpa only [d348814, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348814, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42568 p hg
    simpa only [d348814, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42805 (p : Pattern) (guard : d348815 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348815, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42326 p hg
    simpa only [d348815, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348814 p = 1 := by simpa only [d348815, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42804 p hg
    simpa only [d348815, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42806 (p : Pattern) (guard : d348816 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348807 p = 1 := by simpa only [d348816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42801 p hg
    simpa only [d348816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348815 p = 1 := by simpa only [d348816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42805 p hg
    simpa only [d348816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42807 (p : Pattern) (guard : d348817 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348816 p = 1 := by simpa only [d348817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42806 p hg
    simpa only [d348817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d348817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42808 (p : Pattern) (guard : d348818 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348817 p = 1 := by simpa only [d348818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42807 p hg
    simpa only [d348818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d348818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42809 (p : Pattern) (guard : d348819 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348818 p = 1 := by simpa only [d348819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42808 p hg
    simpa only [d348819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d348819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42810 (p : Pattern) (guard : d348833 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348815 p = 1 := by simpa only [d348833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42805 p hg
    simpa only [d348833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d348833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42811 (p : Pattern) (guard : d348834 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348833 p = 1 := by simpa only [d348834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42810 p hg
    simpa only [d348834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d348834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42812 (p : Pattern) (guard : d348835 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348834 p = 1 := by simpa only [d348835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42811 p hg
    simpa only [d348835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d348835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42813 (p : Pattern) (guard : d348836 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348835 p = 1 := by simpa only [d348836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42812 p hg
    simpa only [d348836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d348836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42814 (p : Pattern) (guard : d349172 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348819 p = 1 := by simpa only [d349172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42809 p hg
    simpa only [d349172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348836 p = 1 := by simpa only [d349172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42813 p hg
    simpa only [d349172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42815 (p : Pattern) (guard : d349173 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d349173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349172 p = 1 := by simpa only [d349173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42814 p hg
    simpa only [d349173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42816 (p : Pattern) (guard : d349174 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d349173 p = 1 := by simpa only [d349174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42815 p hg
    simpa only [d349174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d349174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42817 (p : Pattern) (guard : d349175 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d349175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349174 p = 1 := by simpa only [d349175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42816 p hg
    simpa only [d349175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42818 (p : Pattern) (guard : d349176 p = 1) : d51078 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42505 p hg
    simpa only [d349176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349175 p = 1 := by simpa only [d349176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42817 p hg
    simpa only [d349176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42819 (p : Pattern) (guard : d349177 p = 1) : d51079 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349177, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42324 p hg
    simpa only [d349177, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349176 p = 1 := by simpa only [d349177, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42818 p hg
    simpa only [d349177, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42820 (p : Pattern) (guard : d349178 p = 1) : d51079 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42504 p hg
    simpa only [d349178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349177 p = 1 := by simpa only [d349178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42819 p hg
    simpa only [d349178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42821 (p : Pattern) (guard : d349179 p = 1) : d51079 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d349178 p = 1 := by simpa only [d349179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42820 p hg
    simpa only [d349179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42504 p hg
    simpa only [d349179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42822 (p : Pattern) (guard : d349180 p = 1) : d51079 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d349179 p = 1 := by simpa only [d349180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42821 p hg
    simpa only [d349180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42504 p hg
    simpa only [d349180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42823 (p : Pattern) (guard : d349181 p = 1) : d51079 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d349180 p = 1 := by simpa only [d349181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42822 p hg
    simpa only [d349181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42504 p hg
    simpa only [d349181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42824 (p : Pattern) (guard : d349182 p = 1) : d51137 p ≤ (0 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d349181 p = 1 := by simpa only [d349182, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42823 p hg
    simpa only [d349182, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349182, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42593 p hg
    simpa only [d349182, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42825 (p : Pattern) (guard : d349183 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d349171 p = 1 := by simpa only [d349183, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42750 p hg
    simpa only [d349183, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349182 p = 1 := by simpa only [d349183, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42824 p hg
    simpa only [d349183, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42826 (p : Pattern) (guard : d349184 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349183 p = 1 := by simpa only [d349184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42825 p hg
    simpa only [d349184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42827 (p : Pattern) (guard : d349185 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349184 p = 1 := by simpa only [d349185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42826 p hg
    simpa only [d349185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42828 (p : Pattern) (guard : d349186 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349185 p = 1 := by simpa only [d349186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42827 p hg
    simpa only [d349186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42829 (p : Pattern) (guard : d349187 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349186 p = 1 := by simpa only [d349187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42828 p hg
    simpa only [d349187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42830 (p : Pattern) (guard : d349188 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349187 p = 1 := by simpa only [d349188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42829 p hg
    simpa only [d349188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42831 (p : Pattern) (guard : d349189 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349188 p = 1 := by simpa only [d349189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42830 p hg
    simpa only [d349189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42832 (p : Pattern) (guard : d349190 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349189 p = 1 := by simpa only [d349190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42831 p hg
    simpa only [d349190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42833 (p : Pattern) (guard : d349191 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349190 p = 1 := by simpa only [d349191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42832 p hg
    simpa only [d349191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42834 (p : Pattern) (guard : d349192 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d349192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349191 p = 1 := by simpa only [d349192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42833 p hg
    simpa only [d349192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42835 (p : Pattern) (guard : d349193 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d349163 p = 1 := by simpa only [d349193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42604 p hg
    simpa only [d349193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d349192 p = 1 := by simpa only [d349193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42834 p hg
    simpa only [d349193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42836 (p : Pattern) (guard : d349194 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d349193 p = 1 := by simpa only [d349194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42835 p hg
    simpa only [d349194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42837 (p : Pattern) (guard : d349195 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 260 with
  | false =>
    have hg : d349194 p = 1 := by simpa only [d349195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42836 p hg
    simpa only [d349195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42838 (p : Pattern) (guard : d349196 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 259 with
  | false =>
    have hg : d349195 p = 1 := by simpa only [d349196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42837 p hg
    simpa only [d349196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42839 (p : Pattern) (guard : d349197 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 258 with
  | false =>
    have hg : d349196 p = 1 := by simpa only [d349197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42838 p hg
    simpa only [d349197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42840 (p : Pattern) (guard : d349198 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 257 with
  | false =>
    have hg : d349197 p = 1 := by simpa only [d349198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42839 p hg
    simpa only [d349198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42841 (p : Pattern) (guard : d349199 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 256 with
  | false =>
    have hg : d349198 p = 1 := by simpa only [d349199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42840 p hg
    simpa only [d349199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42842 (p : Pattern) (guard : d349200 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 255 with
  | false =>
    have hg : d349199 p = 1 := by simpa only [d349200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42841 p hg
    simpa only [d349200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42843 (p : Pattern) (guard : d349201 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 254 with
  | false =>
    have hg : d349200 p = 1 := by simpa only [d349201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42842 p hg
    simpa only [d349201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42844 (p : Pattern) (guard : d349202 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 253 with
  | false =>
    have hg : d349201 p = 1 := by simpa only [d349202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42843 p hg
    simpa only [d349202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42845 (p : Pattern) (guard : d349203 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 252 with
  | false =>
    have hg : d349202 p = 1 := by simpa only [d349203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42844 p hg
    simpa only [d349203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42846 (p : Pattern) (guard : d349204 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 251 with
  | false =>
    have hg : d349203 p = 1 := by simpa only [d349204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42845 p hg
    simpa only [d349204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42847 (p : Pattern) (guard : d349205 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 250 with
  | false =>
    have hg : d349204 p = 1 := by simpa only [d349205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42846 p hg
    simpa only [d349205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42848 (p : Pattern) (guard : d349206 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 249 with
  | false =>
    have hg : d349205 p = 1 := by simpa only [d349206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42847 p hg
    simpa only [d349206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42849 (p : Pattern) (guard : d349207 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 245 with
  | false =>
    have hg : d349206 p = 1 := by simpa only [d349207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42848 p hg
    simpa only [d349207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42850 (p : Pattern) (guard : d349208 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 200 with
  | false =>
    have hg : d349207 p = 1 := by simpa only [d349208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42849 p hg
    simpa only [d349208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42851 (p : Pattern) (guard : d349209 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 199 with
  | false =>
    have hg : d349208 p = 1 := by simpa only [d349209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42850 p hg
    simpa only [d349209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42852 (p : Pattern) (guard : d349210 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 186 with
  | false =>
    have hg : d349209 p = 1 := by simpa only [d349210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42851 p hg
    simpa only [d349210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42853 (p : Pattern) (guard : d349211 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 185 with
  | false =>
    have hg : d349210 p = 1 := by simpa only [d349211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42852 p hg
    simpa only [d349211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42854 (p : Pattern) (guard : d349212 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 184 with
  | false =>
    have hg : d349211 p = 1 := by simpa only [d349212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42853 p hg
    simpa only [d349212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42855 (p : Pattern) (guard : d349213 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 181 with
  | false =>
    have hg : d349212 p = 1 := by simpa only [d349213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42854 p hg
    simpa only [d349213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42856 (p : Pattern) (guard : d349214 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 177 with
  | false =>
    have hg : d349213 p = 1 := by simpa only [d349214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42855 p hg
    simpa only [d349214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42857 (p : Pattern) (guard : d349215 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 164 with
  | false =>
    have hg : d349214 p = 1 := by simpa only [d349215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42856 p hg
    simpa only [d349215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42858 (p : Pattern) (guard : d349216 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 156 with
  | false =>
    have hg : d349215 p = 1 := by simpa only [d349216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42857 p hg
    simpa only [d349216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42859 (p : Pattern) (guard : d349217 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 155 with
  | false =>
    have hg : d349216 p = 1 := by simpa only [d349217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42858 p hg
    simpa only [d349217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42860 (p : Pattern) (guard : d349218 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 134 with
  | false =>
    have hg : d349217 p = 1 := by simpa only [d349218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42859 p hg
    simpa only [d349218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42861 (p : Pattern) (guard : d349219 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 133 with
  | false =>
    have hg : d349218 p = 1 := by simpa only [d349219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42860 p hg
    simpa only [d349219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42862 (p : Pattern) (guard : d349220 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 120 with
  | false =>
    have hg : d349219 p = 1 := by simpa only [d349220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42861 p hg
    simpa only [d349220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42863 (p : Pattern) (guard : d349221 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 118 with
  | false =>
    have hg : d349220 p = 1 := by simpa only [d349221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42862 p hg
    simpa only [d349221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42864 (p : Pattern) (guard : d349222 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 114 with
  | false =>
    have hg : d349221 p = 1 := by simpa only [d349222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42863 p hg
    simpa only [d349222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42865 (p : Pattern) (guard : d349223 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 111 with
  | false =>
    have hg : d349222 p = 1 := by simpa only [d349223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42864 p hg
    simpa only [d349223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42866 (p : Pattern) (guard : d349224 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 98 with
  | false =>
    have hg : d349223 p = 1 := by simpa only [d349224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42865 p hg
    simpa only [d349224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42867 (p : Pattern) (guard : d349225 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 97 with
  | false =>
    have hg : d349224 p = 1 := by simpa only [d349225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42866 p hg
    simpa only [d349225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42868 (p : Pattern) (guard : d349226 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 94 with
  | false =>
    have hg : d349225 p = 1 := by simpa only [d349226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42867 p hg
    simpa only [d349226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42869 (p : Pattern) (guard : d349227 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 76 with
  | false =>
    have hg : d349226 p = 1 := by simpa only [d349227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42868 p hg
    simpa only [d349227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42870 (p : Pattern) (guard : d349228 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 67 with
  | false =>
    have hg : d349227 p = 1 := by simpa only [d349228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42869 p hg
    simpa only [d349228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42871 (p : Pattern) (guard : d349229 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 52 with
  | false =>
    have hg : d349228 p = 1 := by simpa only [d349229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42870 p hg
    simpa only [d349229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42872 (p : Pattern) (guard : d349230 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 47 with
  | false =>
    have hg : d349229 p = 1 := by simpa only [d349230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42871 p hg
    simpa only [d349230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42873 (p : Pattern) (guard : d349231 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 46 with
  | false =>
    have hg : d349230 p = 1 := by simpa only [d349231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42872 p hg
    simpa only [d349231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42874 (p : Pattern) (guard : d349232 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 45 with
  | false =>
    have hg : d349231 p = 1 := by simpa only [d349232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42873 p hg
    simpa only [d349232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42875 (p : Pattern) (guard : d349233 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 30 with
  | false =>
    have hg : d349232 p = 1 := by simpa only [d349233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42874 p hg
    simpa only [d349233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42876 (p : Pattern) (guard : d349234 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 29 with
  | false =>
    have hg : d349233 p = 1 := by simpa only [d349234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42875 p hg
    simpa only [d349234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42877 (p : Pattern) (guard : d349235 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 28 with
  | false =>
    have hg : d349234 p = 1 := by simpa only [d349235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42876 p hg
    simpa only [d349235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42878 (p : Pattern) (guard : d349236 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 27 with
  | false =>
    have hg : d349235 p = 1 := by simpa only [d349236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42877 p hg
    simpa only [d349236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42879 (p : Pattern) (guard : d349237 p = 1) : d51138 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 25 with
  | false =>
    have hg : d349236 p = 1 := by simpa only [d349237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42878 p hg
    simpa only [d349237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d349237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42322 p hg
    simpa only [d349237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42880 (p : Pattern) (guard : d0 p = 1) : d51138 p ≤ (-1 : Int) + d51635 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42881 (p : Pattern) (guard : d0 p = 1) : d51138 p ≤ (-2 : Int) + d51635 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42882 (p : Pattern) (guard : d0 p = 1) : d51138 p ≤ (-1 : Int) + d351900 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42883 (p : Pattern) (guard : d0 p = 1) : d51138 p ≤ (-2 : Int) + d351900 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42884 (p : Pattern) (guard : d0 p = 1) : d51138 p ≤ (-1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42885 (p : Pattern) (guard : d0 p = 1) : d51138 p ≤ (-2 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42886 (p : Pattern) (guard : d0 p = 1) : d51138 p ≤ (-1 : Int) + d50493 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42887 (p : Pattern) (guard : d0 p = 1) : d51138 p ≤ (-2 : Int) + d50493 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42888 (p : Pattern) (guard : d0 p = 1) : d51635 p ≤ (-1 : Int) + d50493 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42889 (p : Pattern) (guard : d0 p = 1) : d51635 p ≤ (-2 : Int) + d50493 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42890 (p : Pattern) (guard : d0 p = 1) : d51635 p ≤ (-1 : Int) + d50823 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42891 (p : Pattern) (guard : d0 p = 1) : d51635 p ≤ (-2 : Int) + d50823 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42892 (p : Pattern) (guard : d0 p = 1) : d51635 p ≤ (-1 : Int) + d51138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42893 (p : Pattern) (guard : d0 p = 1) : d51635 p ≤ (-2 : Int) + d51138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42894 (p : Pattern) (guard : d0 p = 1) : d51635 p ≤ (8 : Int) + d338883 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42895 (p : Pattern) (guard : d0 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42896 (p : Pattern) (guard : d0 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42897 (p : Pattern) (guard : d0 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42898 (p : Pattern) (guard : d0 p = 1) : d51329 p ≤ (8 : Int) + d338724 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42899 (p : Pattern) (guard : d0 p = 1) : d51313 p ≤ (8 : Int) + d338703 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42900 (p : Pattern) (guard : d0 p = 1) : d51283 p ≤ (8 : Int) + d338708 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42901 (p : Pattern) (guard : d0 p = 1) : d51286 p ≤ (8 : Int) + d338684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42902 (p : Pattern) (guard : d342715 p = 1) : d51288 p ≤ (8 : Int) + d338690 p := by
  have ha := bounds51288 p
  have hb := bounds338690 p
  omega
theorem compare42903 (p : Pattern) (guard : d342716 p = 1) : d51289 p ≤ (8 : Int) + d338691 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342716, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42901 p hg
    simpa only [d342716, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342715 p = 1 := by simpa only [d342716, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42902 p hg
    simpa only [d342716, d51289, d338691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42904 (p : Pattern) (guard : d0 p = 1) : d51292 p ≤ (8 : Int) + d338711 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42905 (p : Pattern) (guard : d342717 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 160 with
  | false =>
    have hg : d342716 p = 1 := by simpa only [d342717, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42903 p hg
    simpa only [d342717, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342717, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42904 p hg
    simpa only [d342717, d51293, d338712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42906 (p : Pattern) (guard : d0 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42907 (p : Pattern) (guard : d342718 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 159 with
  | false =>
    have hg : d342717 p = 1 := by simpa only [d342718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42905 p hg
    simpa only [d342718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42906 p hg
    simpa only [d342718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42908 (p : Pattern) (guard : d342719 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 158 with
  | false =>
    have hg : d342718 p = 1 := by simpa only [d342719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42907 p hg
    simpa only [d342719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42906 p hg
    simpa only [d342719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42909 (p : Pattern) (guard : d342720 p = 1) : d51293 p ≤ (8 : Int) + d338712 p := by
  cases selected : p 157 with
  | false =>
    have hg : d342719 p = 1 := by simpa only [d342720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42908 p hg
    simpa only [d342720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42906 p hg
    simpa only [d342720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42910 (p : Pattern) (guard : d342721 p = 1) : d51294 p ≤ (8 : Int) + d338713 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342721, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42900 p hg
    simpa only [d342721, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342720 p = 1 := by simpa only [d342721, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42909 p hg
    simpa only [d342721, d51294, d338713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42911 (p : Pattern) (guard : d342722 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342722, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42899 p hg
    simpa only [d342722, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342721 p = 1 := by simpa only [d342722, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42910 p hg
    simpa only [d342722, d51314, d338714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42912 (p : Pattern) (guard : d0 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42913 (p : Pattern) (guard : d342723 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342722 p = 1 := by simpa only [d342723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42911 p hg
    simpa only [d342723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d342723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42914 (p : Pattern) (guard : d342724 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 135 with
  | false =>
    have hg : d342723 p = 1 := by simpa only [d342724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42913 p hg
    simpa only [d342724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d342724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42915 (p : Pattern) (guard : d342725 p = 1) : d51314 p ≤ (8 : Int) + d338714 p := by
  cases selected : p 119 with
  | false =>
    have hg : d342724 p = 1 := by simpa only [d342725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42914 p hg
    simpa only [d342725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42912 p hg
    simpa only [d342725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42916 (p : Pattern) (guard : d0 p = 1) : d51315 p ≤ (8 : Int) + d338725 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42917 (p : Pattern) (guard : d342726 p = 1) : d51316 p ≤ (8 : Int) + d338726 p := by
  cases selected : p 116 with
  | false =>
    have hg : d342725 p = 1 := by simpa only [d342726, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42915 p hg
    simpa only [d342726, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342726, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42916 p hg
    simpa only [d342726, d51316, d338726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42918 (p : Pattern) (guard : d342727 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342727, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42898 p hg
    simpa only [d342727, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342726 p = 1 := by simpa only [d342727, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42917 p hg
    simpa only [d342727, d51330, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42919 (p : Pattern) (guard : d342728 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342727 p = 1 := by simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42918 p hg
    simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42920 (p : Pattern) (guard : d342729 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342728 p = 1 := by simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42919 p hg
    simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42921 (p : Pattern) (guard : d342730 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342729 p = 1 := by simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42920 p hg
    simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42922 (p : Pattern) (guard : d342731 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342730 p = 1 := by simpa only [d342731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42921 p hg
    simpa only [d342731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42923 (p : Pattern) (guard : d342732 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342731 p = 1 := by simpa only [d342732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42922 p hg
    simpa only [d342732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42924 (p : Pattern) (guard : d342733 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d342732 p = 1 := by simpa only [d342733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42923 p hg
    simpa only [d342733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42925 (p : Pattern) (guard : d342734 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342733 p = 1 := by simpa only [d342734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42924 p hg
    simpa only [d342734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42926 (p : Pattern) (guard : d342735 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342734 p = 1 := by simpa only [d342735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42925 p hg
    simpa only [d342735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42927 (p : Pattern) (guard : d342736 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342735 p = 1 := by simpa only [d342736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42926 p hg
    simpa only [d342736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42928 (p : Pattern) (guard : d342737 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342737, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342737, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342736 p = 1 := by simpa only [d342737, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42927 p hg
    simpa only [d342737, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42929 (p : Pattern) (guard : d0 p = 1) : d51305 p ≤ (8 : Int) + d338724 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42930 (p : Pattern) (guard : d342727 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342727, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42929 p hg
    simpa only [d342727, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342726 p = 1 := by simpa only [d342727, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42917 p hg
    simpa only [d342727, d51317, d338727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42931 (p : Pattern) (guard : d342728 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342727 p = 1 := by simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42930 p hg
    simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42932 (p : Pattern) (guard : d342729 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342728 p = 1 := by simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42931 p hg
    simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42933 (p : Pattern) (guard : d342730 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342729 p = 1 := by simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42932 p hg
    simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42934 (p : Pattern) (guard : d342731 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342730 p = 1 := by simpa only [d342731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42933 p hg
    simpa only [d342731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42935 (p : Pattern) (guard : d342732 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342731 p = 1 := by simpa only [d342732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42934 p hg
    simpa only [d342732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42936 (p : Pattern) (guard : d342733 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d342732 p = 1 := by simpa only [d342733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42935 p hg
    simpa only [d342733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42937 (p : Pattern) (guard : d342734 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342733 p = 1 := by simpa only [d342734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42936 p hg
    simpa only [d342734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42938 (p : Pattern) (guard : d342735 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342734 p = 1 := by simpa only [d342735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42937 p hg
    simpa only [d342735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42939 (p : Pattern) (guard : d342736 p = 1) : d51317 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342735 p = 1 := by simpa only [d342736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42938 p hg
    simpa only [d342736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42940 (p : Pattern) (guard : d342738 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342730 p = 1 := by simpa only [d342738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42921 p hg
    simpa only [d342738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42941 (p : Pattern) (guard : d342739 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342738 p = 1 := by simpa only [d342739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42940 p hg
    simpa only [d342739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42942 (p : Pattern) (guard : d342740 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 90 with
  | false =>
    have hg : d342739 p = 1 := by simpa only [d342740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42941 p hg
    simpa only [d342740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42943 (p : Pattern) (guard : d342741 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342740 p = 1 := by simpa only [d342741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42942 p hg
    simpa only [d342741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42944 (p : Pattern) (guard : d342742 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342741 p = 1 := by simpa only [d342742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42943 p hg
    simpa only [d342742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42945 (p : Pattern) (guard : d342743 p = 1) : d51330 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42897 p hg
    simpa only [d342743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342742 p = 1 := by simpa only [d342743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42944 p hg
    simpa only [d342743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42946 (p : Pattern) (guard : d342744 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 71 with
  | false =>
    have hg : d342736 p = 1 := by simpa only [d342744, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42939 p hg
    simpa only [d342744, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342743 p = 1 := by simpa only [d342744, d51331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42945 p hg
    simpa only [d342744, d51331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42947 (p : Pattern) (guard : d342745 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 70 with
  | false =>
    have hg : d342737 p = 1 := by simpa only [d342745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42928 p hg
    simpa only [d342745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342744 p = 1 := by simpa only [d342745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42946 p hg
    simpa only [d342745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42948 (p : Pattern) (guard : d342746 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 69 with
  | false =>
    have hg : d342745 p = 1 := by simpa only [d342746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42947 p hg
    simpa only [d342746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d342746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42949 (p : Pattern) (guard : d342747 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 51 with
  | false =>
    have hg : d342746 p = 1 := by simpa only [d342747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42948 p hg
    simpa only [d342747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d342747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42950 (p : Pattern) (guard : d342748 p = 1) : d51331 p ≤ (8 : Int) + d338727 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42895 p hg
    simpa only [d342748, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342747 p = 1 := by simpa only [d342748, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42949 p hg
    simpa only [d342748, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42951 (p : Pattern) (guard : d0 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42952 (p : Pattern) (guard : d0 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42953 (p : Pattern) (guard : d0 p = 1) : d51460 p ≤ (8 : Int) + d338782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42954 (p : Pattern) (guard : d0 p = 1) : d51464 p ≤ (8 : Int) + d338765 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42955 (p : Pattern) (guard : d0 p = 1) : d51442 p ≤ (8 : Int) + d338770 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42956 (p : Pattern) (guard : d0 p = 1) : d51445 p ≤ (8 : Int) + d338753 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42957 (p : Pattern) (guard : d342715 p = 1) : d51447 p ≤ (8 : Int) + d338755 p := by
  have ha := bounds51447 p
  have hb := bounds338755 p
  omega
theorem compare42958 (p : Pattern) (guard : d342716 p = 1) : d51448 p ≤ (8 : Int) + d338756 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342716, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42956 p hg
    simpa only [d342716, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342715 p = 1 := by simpa only [d342716, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42957 p hg
    simpa only [d342716, d51448, d338756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42959 (p : Pattern) (guard : d0 p = 1) : d51451 p ≤ (8 : Int) + d338773 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42960 (p : Pattern) (guard : d342717 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 160 with
  | false =>
    have hg : d342716 p = 1 := by simpa only [d342717, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42958 p hg
    simpa only [d342717, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342717, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42959 p hg
    simpa only [d342717, d51452, d338774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42961 (p : Pattern) (guard : d0 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42962 (p : Pattern) (guard : d342718 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 159 with
  | false =>
    have hg : d342717 p = 1 := by simpa only [d342718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42960 p hg
    simpa only [d342718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42961 p hg
    simpa only [d342718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42963 (p : Pattern) (guard : d342719 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 158 with
  | false =>
    have hg : d342718 p = 1 := by simpa only [d342719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42962 p hg
    simpa only [d342719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42961 p hg
    simpa only [d342719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42964 (p : Pattern) (guard : d342720 p = 1) : d51452 p ≤ (8 : Int) + d338774 p := by
  cases selected : p 157 with
  | false =>
    have hg : d342719 p = 1 := by simpa only [d342720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42963 p hg
    simpa only [d342720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42961 p hg
    simpa only [d342720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42965 (p : Pattern) (guard : d342721 p = 1) : d51453 p ≤ (8 : Int) + d338775 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342721, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42955 p hg
    simpa only [d342721, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342720 p = 1 := by simpa only [d342721, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42964 p hg
    simpa only [d342721, d51453, d338775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42966 (p : Pattern) (guard : d342722 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342722, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42954 p hg
    simpa only [d342722, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342721 p = 1 := by simpa only [d342722, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42965 p hg
    simpa only [d342722, d51465, d338776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42967 (p : Pattern) (guard : d0 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42968 (p : Pattern) (guard : d342723 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 136 with
  | false =>
    have hg : d342722 p = 1 := by simpa only [d342723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42966 p hg
    simpa only [d342723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d342723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42969 (p : Pattern) (guard : d342724 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 135 with
  | false =>
    have hg : d342723 p = 1 := by simpa only [d342724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42968 p hg
    simpa only [d342724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d342724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42970 (p : Pattern) (guard : d342725 p = 1) : d51465 p ≤ (8 : Int) + d338776 p := by
  cases selected : p 119 with
  | false =>
    have hg : d342724 p = 1 := by simpa only [d342725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42969 p hg
    simpa only [d342725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42967 p hg
    simpa only [d342725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42971 (p : Pattern) (guard : d0 p = 1) : d51466 p ≤ (8 : Int) + d338783 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42972 (p : Pattern) (guard : d342726 p = 1) : d51467 p ≤ (8 : Int) + d338784 p := by
  cases selected : p 116 with
  | false =>
    have hg : d342725 p = 1 := by simpa only [d342726, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42970 p hg
    simpa only [d342726, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342726, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42971 p hg
    simpa only [d342726, d51467, d338784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42973 (p : Pattern) (guard : d342727 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342727, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42953 p hg
    simpa only [d342727, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342726 p = 1 := by simpa only [d342727, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42972 p hg
    simpa only [d342727, d51468, d338785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42974 (p : Pattern) (guard : d342728 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 113 with
  | false =>
    have hg : d342727 p = 1 := by simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42973 p hg
    simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42975 (p : Pattern) (guard : d342729 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 96 with
  | false =>
    have hg : d342728 p = 1 := by simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42974 p hg
    simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42976 (p : Pattern) (guard : d342730 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 95 with
  | false =>
    have hg : d342729 p = 1 := by simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42975 p hg
    simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42977 (p : Pattern) (guard : d342738 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 93 with
  | false =>
    have hg : d342730 p = 1 := by simpa only [d342738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42976 p hg
    simpa only [d342738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42978 (p : Pattern) (guard : d342739 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 91 with
  | false =>
    have hg : d342738 p = 1 := by simpa only [d342739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42977 p hg
    simpa only [d342739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42979 (p : Pattern) (guard : d342740 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 90 with
  | false =>
    have hg : d342739 p = 1 := by simpa only [d342740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42978 p hg
    simpa only [d342740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42980 (p : Pattern) (guard : d342741 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 89 with
  | false =>
    have hg : d342740 p = 1 := by simpa only [d342741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42979 p hg
    simpa only [d342741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42981 (p : Pattern) (guard : d342742 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342741 p = 1 := by simpa only [d342742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42980 p hg
    simpa only [d342742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42982 (p : Pattern) (guard : d342743 p = 1) : d51468 p ≤ (8 : Int) + d338785 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42952 p hg
    simpa only [d342743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342742 p = 1 := by simpa only [d342743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42981 p hg
    simpa only [d342743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42983 (p : Pattern) (guard : d342749 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342749, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42896 p hg
    simpa only [d342749, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342743 p = 1 := by simpa only [d342749, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42982 p hg
    simpa only [d342749, d51469, d338786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42984 (p : Pattern) (guard : d342750 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d342750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d342750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342749 p = 1 := by simpa only [d342750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42983 p hg
    simpa only [d342750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42985 (p : Pattern) (guard : d342751 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 69 with
  | false =>
    have hg : d342750 p = 1 := by simpa only [d342751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42984 p hg
    simpa only [d342751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d342751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42986 (p : Pattern) (guard : d342752 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 51 with
  | false =>
    have hg : d342751 p = 1 := by simpa only [d342752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42985 p hg
    simpa only [d342752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d342752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42987 (p : Pattern) (guard : d342753 p = 1) : d51469 p ≤ (8 : Int) + d338786 p := by
  cases selected : p 50 with
  | false =>
    have hg : d342752 p = 1 := by simpa only [d342753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42986 p hg
    simpa only [d342753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d342753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42951 p hg
    simpa only [d342753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42988 (p : Pattern) (guard : d342754 p = 1) : d51470 p ≤ (8 : Int) + d338787 p := by
  cases selected : p 49 with
  | false =>
    have hg : d342748 p = 1 := by simpa only [d342754, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42950 p hg
    simpa only [d342754, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d342753 p = 1 := by simpa only [d342754, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42987 p hg
    simpa only [d342754, d51470, d338787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42989 (p : Pattern) (guard : d0 p = 1) : d51542 p ≤ (8 : Int) + d338826 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42990 (p : Pattern) (guard : d0 p = 1) : d51541 p ≤ (8 : Int) + d338825 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42991 (p : Pattern) (guard : d0 p = 1) : d51508 p ≤ (8 : Int) + d338805 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42992 (p : Pattern) (guard : d0 p = 1) : d51523 p ≤ (8 : Int) + d338813 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42993 (p : Pattern) (guard : d0 p = 1) : d51528 p ≤ (8 : Int) + d338681 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42994 (p : Pattern) (guard : d0 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42995 (p : Pattern) (guard : d13 p = 1) : d2 p ≤ (8 : Int) + d2 p := by
  omega
theorem compare42996 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (8 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare42997 (p : Pattern) (guard : d14 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 247 with
  | false =>
    have hg : d13 p = 1 := by simpa only [d14, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42995 p hg
    simpa only [d14, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14, d47629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42996 p hg
    simpa only [d14, d47629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42998 (p : Pattern) (guard : d1084 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42997 p hg
    simpa only [d1084, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42999 (p : Pattern) (guard : d1085 p = 1) : d47629 p ≤ (8 : Int) + d2 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42998 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42994 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
