import NetHack.Soko22Hazard87.Compare167
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare42000 (p : Pattern) (guard : d258108 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258107 p = 1 := by simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41999 p hg
    simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42001 (p : Pattern) (guard : d258109 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258108 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42000 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42002 (p : Pattern) (guard : d348629 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d337473 p = 1 := by simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41998 p hg
    simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42001 p hg
    simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42003 (p : Pattern) (guard : d348630 p = 1) : d50874 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d348629 p = 1 := by simpa only [d348630, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42002 p hg
    simpa only [d348630, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348630, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41578 p hg
    simpa only [d348630, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42004 (p : Pattern) (guard : d348631 p = 1) : d50874 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d348630 p = 1 := by simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42003 p hg
    simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41563 p hg
    simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42005 (p : Pattern) (guard : d348776 p = 1) : d50874 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41563 p hg
    simpa only [d348776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348631 p = 1 := by simpa only [d348776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42004 p hg
    simpa only [d348776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42006 (p : Pattern) (guard : d348632 p = 1) : d51067 p ≤ (1 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348631 p = 1 := by simpa only [d348632, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41701 p hg
    simpa only [d348632, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348632, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41482 p hg
    simpa only [d348632, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42007 (p : Pattern) (guard : d348777 p = 1) : d51068 p ≤ (1 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348776 p = 1 := by simpa only [d348777, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42005 p hg
    simpa only [d348777, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348632 p = 1 := by simpa only [d348777, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42006 p hg
    simpa only [d348777, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42008 (p : Pattern) (guard : d308 p = 1) : d6 p ≤ (1 : Int) + d6 p := by
  omega
theorem compare42009 (p : Pattern) (guard : d1519 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 246 with
  | false =>
    have hg : d308 p = 1 := by simpa only [d1519, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42008 p hg
    simpa only [d1519, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1519, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41586 p hg
    simpa only [d1519, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42010 (p : Pattern) (guard : d1531 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1519 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42009 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d1531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42011 (p : Pattern) (guard : d1547 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1531 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42010 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d1547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42012 (p : Pattern) (guard : d39244 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1547 p = 1 := by simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42011 p hg
    simpa only [d39244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42013 (p : Pattern) (guard : d337457 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d39244 p = 1 := by simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42012 p hg
    simpa only [d337457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42014 (p : Pattern) (guard : d337458 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d337457 p = 1 := by simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42013 p hg
    simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d337458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42015 (p : Pattern) (guard : d337473 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d337458 p = 1 := by simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42014 p hg
    simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d337473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42016 (p : Pattern) (guard : d258107 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d39244 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42012 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d258107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42017 (p : Pattern) (guard : d258108 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d258107 p = 1 := by simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42016 p hg
    simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d258108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42018 (p : Pattern) (guard : d258109 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d258108 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42017 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d258109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42019 (p : Pattern) (guard : d348629 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d337473 p = 1 := by simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42015 p hg
    simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258109 p = 1 := by simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42018 p hg
    simpa only [d348629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42020 (p : Pattern) (guard : d348630 p = 1) : d50900 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d348629 p = 1 := by simpa only [d348630, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42019 p hg
    simpa only [d348630, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348630, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41598 p hg
    simpa only [d348630, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42021 (p : Pattern) (guard : d348631 p = 1) : d50900 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d348630 p = 1 := by simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42020 p hg
    simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41600 p hg
    simpa only [d348631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42022 (p : Pattern) (guard : d348632 p = 1) : d50908 p ≤ (1 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348631 p = 1 := by simpa only [d348632, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42021 p hg
    simpa only [d348632, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348632, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d348632, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42023 (p : Pattern) (guard : d348633 p = 1) : d50909 p ≤ (1 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348632 p = 1 := by simpa only [d348633, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42022 p hg
    simpa only [d348633, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348633, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d348633, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42024 (p : Pattern) (guard : d348778 p = 1) : d51069 p ≤ (1 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d348777 p = 1 := by simpa only [d348778, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42007 p hg
    simpa only [d348778, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348633 p = 1 := by simpa only [d348778, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42023 p hg
    simpa only [d348778, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42025 (p : Pattern) (guard : d348779 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d348778 p = 1 := by simpa only [d348779, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42024 p hg
    simpa only [d348779, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348779, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41605 p hg
    simpa only [d348779, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42026 (p : Pattern) (guard : d348780 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41562 p hg
    simpa only [d348780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348779 p = 1 := by simpa only [d348780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42025 p hg
    simpa only [d348780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42027 (p : Pattern) (guard : d348781 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41562 p hg
    simpa only [d348781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348780 p = 1 := by simpa only [d348781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42026 p hg
    simpa only [d348781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42028 (p : Pattern) (guard : d348782 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41562 p hg
    simpa only [d348782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348781 p = 1 := by simpa only [d348782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42027 p hg
    simpa only [d348782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42029 (p : Pattern) (guard : d348783 p = 1) : d51074 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348783, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41561 p hg
    simpa only [d348783, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348782 p = 1 := by simpa only [d348783, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42028 p hg
    simpa only [d348783, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42030 (p : Pattern) (guard : d348784 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348784, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41560 p hg
    simpa only [d348784, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348783 p = 1 := by simpa only [d348784, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42029 p hg
    simpa only [d348784, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42031 (p : Pattern) (guard : d348785 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d348779 p = 1 := by simpa only [d348785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42025 p hg
    simpa only [d348785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41562 p hg
    simpa only [d348785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42032 (p : Pattern) (guard : d348786 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d348780 p = 1 := by simpa only [d348786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42026 p hg
    simpa only [d348786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348785 p = 1 := by simpa only [d348786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42031 p hg
    simpa only [d348786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42033 (p : Pattern) (guard : d348787 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348781 p = 1 := by simpa only [d348787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42027 p hg
    simpa only [d348787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348786 p = 1 := by simpa only [d348787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42032 p hg
    simpa only [d348787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42034 (p : Pattern) (guard : d348788 p = 1) : d51074 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348788, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41561 p hg
    simpa only [d348788, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348787 p = 1 := by simpa only [d348788, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42033 p hg
    simpa only [d348788, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42035 (p : Pattern) (guard : d348789 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348789, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41560 p hg
    simpa only [d348789, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348788 p = 1 := by simpa only [d348789, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42034 p hg
    simpa only [d348789, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42036 (p : Pattern) (guard : d348790 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348784 p = 1 := by simpa only [d348790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42030 p hg
    simpa only [d348790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348789 p = 1 := by simpa only [d348790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42035 p hg
    simpa only [d348790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42037 (p : Pattern) (guard : d348791 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41562 p hg
    simpa only [d348791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348785 p = 1 := by simpa only [d348791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42031 p hg
    simpa only [d348791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42038 (p : Pattern) (guard : d348792 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348781 p = 1 := by simpa only [d348792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42027 p hg
    simpa only [d348792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348791 p = 1 := by simpa only [d348792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42037 p hg
    simpa only [d348792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42039 (p : Pattern) (guard : d348793 p = 1) : d51074 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348793, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41561 p hg
    simpa only [d348793, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348792 p = 1 := by simpa only [d348793, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42038 p hg
    simpa only [d348793, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42040 (p : Pattern) (guard : d348794 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348794, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41560 p hg
    simpa only [d348794, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348793 p = 1 := by simpa only [d348794, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42039 p hg
    simpa only [d348794, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42041 (p : Pattern) (guard : d348795 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348791 p = 1 := by simpa only [d348795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42037 p hg
    simpa only [d348795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41562 p hg
    simpa only [d348795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42042 (p : Pattern) (guard : d348796 p = 1) : d51074 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348796, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41561 p hg
    simpa only [d348796, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348795 p = 1 := by simpa only [d348796, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42041 p hg
    simpa only [d348796, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42043 (p : Pattern) (guard : d348797 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348797, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41560 p hg
    simpa only [d348797, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348796 p = 1 := by simpa only [d348797, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42042 p hg
    simpa only [d348797, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42044 (p : Pattern) (guard : d348798 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348794 p = 1 := by simpa only [d348798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42040 p hg
    simpa only [d348798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348797 p = 1 := by simpa only [d348798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42043 p hg
    simpa only [d348798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42045 (p : Pattern) (guard : d348799 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348790 p = 1 := by simpa only [d348799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42036 p hg
    simpa only [d348799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348798 p = 1 := by simpa only [d348799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42044 p hg
    simpa only [d348799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42046 (p : Pattern) (guard : d348800 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348799 p = 1 := by simpa only [d348800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42045 p hg
    simpa only [d348800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41627 p hg
    simpa only [d348800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42047 (p : Pattern) (guard : d348801 p = 1) : d51077 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348800 p = 1 := by simpa only [d348801, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42046 p hg
    simpa only [d348801, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348801, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41629 p hg
    simpa only [d348801, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42048 (p : Pattern) (guard : d348802 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348802, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41223 p hg
    simpa only [d348802, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348801 p = 1 := by simpa only [d348802, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42047 p hg
    simpa only [d348802, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42049 (p : Pattern) (guard : d348803 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348797 p = 1 := by simpa only [d348803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42043 p hg
    simpa only [d348803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41627 p hg
    simpa only [d348803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42050 (p : Pattern) (guard : d348804 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348798 p = 1 := by simpa only [d348804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42044 p hg
    simpa only [d348804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348803 p = 1 := by simpa only [d348804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42049 p hg
    simpa only [d348804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42051 (p : Pattern) (guard : d348805 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348804 p = 1 := by simpa only [d348805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42050 p hg
    simpa only [d348805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41627 p hg
    simpa only [d348805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42052 (p : Pattern) (guard : d348806 p = 1) : d51077 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348805 p = 1 := by simpa only [d348806, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42051 p hg
    simpa only [d348806, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348806, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41629 p hg
    simpa only [d348806, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42053 (p : Pattern) (guard : d348807 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348807, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41223 p hg
    simpa only [d348807, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348806 p = 1 := by simpa only [d348807, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42052 p hg
    simpa only [d348807, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42054 (p : Pattern) (guard : d348808 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348802 p = 1 := by simpa only [d348808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42048 p hg
    simpa only [d348808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348807 p = 1 := by simpa only [d348808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42053 p hg
    simpa only [d348808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42055 (p : Pattern) (guard : d348809 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348808 p = 1 := by simpa only [d348809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42054 p hg
    simpa only [d348809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42056 (p : Pattern) (guard : d348810 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348809 p = 1 := by simpa only [d348810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42055 p hg
    simpa only [d348810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42057 (p : Pattern) (guard : d348811 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348810 p = 1 := by simpa only [d348811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42056 p hg
    simpa only [d348811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42058 (p : Pattern) (guard : d348812 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d348803 p = 1 := by simpa only [d348812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42049 p hg
    simpa only [d348812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41627 p hg
    simpa only [d348812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42059 (p : Pattern) (guard : d348813 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348812 p = 1 := by simpa only [d348813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42058 p hg
    simpa only [d348813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41627 p hg
    simpa only [d348813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42060 (p : Pattern) (guard : d348814 p = 1) : d51077 p ≤ (1 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348813 p = 1 := by simpa only [d348814, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42059 p hg
    simpa only [d348814, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348814, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41629 p hg
    simpa only [d348814, d51077, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42061 (p : Pattern) (guard : d348815 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348815, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41223 p hg
    simpa only [d348815, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348814 p = 1 := by simpa only [d348815, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42060 p hg
    simpa only [d348815, d51078, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42062 (p : Pattern) (guard : d348816 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348807 p = 1 := by simpa only [d348816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42053 p hg
    simpa only [d348816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348815 p = 1 := by simpa only [d348816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42061 p hg
    simpa only [d348816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42063 (p : Pattern) (guard : d348817 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348816 p = 1 := by simpa only [d348817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42062 p hg
    simpa only [d348817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42064 (p : Pattern) (guard : d348818 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348817 p = 1 := by simpa only [d348818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42063 p hg
    simpa only [d348818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42065 (p : Pattern) (guard : d348819 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348818 p = 1 := by simpa only [d348819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42064 p hg
    simpa only [d348819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42066 (p : Pattern) (guard : d348820 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348811 p = 1 := by simpa only [d348820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42057 p hg
    simpa only [d348820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348819 p = 1 := by simpa only [d348820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42065 p hg
    simpa only [d348820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42067 (p : Pattern) (guard : d348821 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348820 p = 1 := by simpa only [d348821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42066 p hg
    simpa only [d348821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42068 (p : Pattern) (guard : d348822 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348807 p = 1 := by simpa only [d348822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42053 p hg
    simpa only [d348822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42069 (p : Pattern) (guard : d348823 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348822 p = 1 := by simpa only [d348823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42068 p hg
    simpa only [d348823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42070 (p : Pattern) (guard : d348824 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348823 p = 1 := by simpa only [d348824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42069 p hg
    simpa only [d348824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42071 (p : Pattern) (guard : d348825 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348824 p = 1 := by simpa only [d348825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42070 p hg
    simpa only [d348825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42072 (p : Pattern) (guard : d348826 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348825 p = 1 := by simpa only [d348826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42071 p hg
    simpa only [d348826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42073 (p : Pattern) (guard : d348827 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348826 p = 1 := by simpa only [d348827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42072 p hg
    simpa only [d348827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42074 (p : Pattern) (guard : d348828 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348821 p = 1 := by simpa only [d348828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42067 p hg
    simpa only [d348828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348827 p = 1 := by simpa only [d348828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42073 p hg
    simpa only [d348828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42075 (p : Pattern) (guard : d348829 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348828 p = 1 := by simpa only [d348829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42074 p hg
    simpa only [d348829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42076 (p : Pattern) (guard : d348830 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348829 p = 1 := by simpa only [d348830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42075 p hg
    simpa only [d348830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42077 (p : Pattern) (guard : d348831 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348831, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348831, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348830 p = 1 := by simpa only [d348831, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42076 p hg
    simpa only [d348831, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42078 (p : Pattern) (guard : d348832 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41558 p hg
    simpa only [d348832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348831 p = 1 := by simpa only [d348832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42077 p hg
    simpa only [d348832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42079 (p : Pattern) (guard : d348833 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348815 p = 1 := by simpa only [d348833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42061 p hg
    simpa only [d348833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42080 (p : Pattern) (guard : d348834 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348833 p = 1 := by simpa only [d348834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42079 p hg
    simpa only [d348834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42081 (p : Pattern) (guard : d348835 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348834 p = 1 := by simpa only [d348835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42080 p hg
    simpa only [d348835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42082 (p : Pattern) (guard : d348836 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348835 p = 1 := by simpa only [d348836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42081 p hg
    simpa only [d348836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42083 (p : Pattern) (guard : d348837 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348836 p = 1 := by simpa only [d348837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42082 p hg
    simpa only [d348837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42084 (p : Pattern) (guard : d348838 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348837 p = 1 := by simpa only [d348838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42083 p hg
    simpa only [d348838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42085 (p : Pattern) (guard : d348839 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d348838 p = 1 := by simpa only [d348839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42084 p hg
    simpa only [d348839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42086 (p : Pattern) (guard : d348840 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348839 p = 1 := by simpa only [d348840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42085 p hg
    simpa only [d348840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42087 (p : Pattern) (guard : d348841 p = 1) : d51078 p ≤ (1 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41559 p hg
    simpa only [d348841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348840 p = 1 := by simpa only [d348841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42086 p hg
    simpa only [d348841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42088 (p : Pattern) (guard : d348842 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348842, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348842, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348841 p = 1 := by simpa only [d348842, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42087 p hg
    simpa only [d348842, d51079, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42089 (p : Pattern) (guard : d348843 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41558 p hg
    simpa only [d348843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348842 p = 1 := by simpa only [d348843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42088 p hg
    simpa only [d348843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42090 (p : Pattern) (guard : d348844 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d348832 p = 1 := by simpa only [d348844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42078 p hg
    simpa only [d348844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348843 p = 1 := by simpa only [d348844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42089 p hg
    simpa only [d348844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42091 (p : Pattern) (guard : d348845 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d348844 p = 1 := by simpa only [d348845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42090 p hg
    simpa only [d348845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41558 p hg
    simpa only [d348845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42092 (p : Pattern) (guard : d348846 p = 1) : d51079 p ≤ (1 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d348845 p = 1 := by simpa only [d348846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42091 p hg
    simpa only [d348846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41558 p hg
    simpa only [d348846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42093 (p : Pattern) (guard : d348847 p = 1) : d51137 p ≤ (1 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d348846 p = 1 := by simpa only [d348847, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42092 p hg
    simpa only [d348847, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348847, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41676 p hg
    simpa only [d348847, d51137, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42094 (p : Pattern) (guard : d348848 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d348775 p = 1 := by simpa only [d348848, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41990 p hg
    simpa only [d348848, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348847 p = 1 := by simpa only [d348848, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42093 p hg
    simpa only [d348848, d51138, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42095 (p : Pattern) (guard : d348849 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348848 p = 1 := by simpa only [d348849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42094 p hg
    simpa only [d348849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42096 (p : Pattern) (guard : d348850 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348849 p = 1 := by simpa only [d348850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42095 p hg
    simpa only [d348850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42097 (p : Pattern) (guard : d348851 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348850 p = 1 := by simpa only [d348851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42096 p hg
    simpa only [d348851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42098 (p : Pattern) (guard : d348852 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348851 p = 1 := by simpa only [d348852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42097 p hg
    simpa only [d348852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42099 (p : Pattern) (guard : d348853 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348852 p = 1 := by simpa only [d348853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42098 p hg
    simpa only [d348853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42100 (p : Pattern) (guard : d348854 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348853 p = 1 := by simpa only [d348854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42099 p hg
    simpa only [d348854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42101 (p : Pattern) (guard : d348855 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348854 p = 1 := by simpa only [d348855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42100 p hg
    simpa only [d348855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42102 (p : Pattern) (guard : d348856 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348855 p = 1 := by simpa only [d348856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42101 p hg
    simpa only [d348856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42103 (p : Pattern) (guard : d348857 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41219 p hg
    simpa only [d348857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348856 p = 1 := by simpa only [d348857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42102 p hg
    simpa only [d348857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42104 (p : Pattern) (guard : d348858 p = 1) : d51138 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d348628 p = 1 := by simpa only [d348858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41687 p hg
    simpa only [d348858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348857 p = 1 := by simpa only [d348858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42103 p hg
    simpa only [d348858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42105 (p : Pattern) (guard : d307 p = 1) : d4 p ≤ (1 : Int) + d4 p := by
  omega
theorem compare42106 (p : Pattern) (guard : d1997 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42105 p hg
    simpa only [d1997, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41230 p hg
    simpa only [d1997, d50838, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42107 (p : Pattern) (guard : d1998 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42106 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42108 (p : Pattern) (guard : d2013 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42106 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42109 (p : Pattern) (guard : d2014 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42107 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42108 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42110 (p : Pattern) (guard : d257871 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42109 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42111 (p : Pattern) (guard : d257872 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42110 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42112 (p : Pattern) (guard : d257873 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257872 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42111 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42113 (p : Pattern) (guard : d257874 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257873 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42112 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42114 (p : Pattern) (guard : d259291 p = 1) : d50838 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42113 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41228 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42115 (p : Pattern) (guard : d259292 p = 1) : d50840 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259291 p = 1 := by simpa only [d259292, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42114 p hg
    simpa only [d259292, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259292, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41242 p hg
    simpa only [d259292, d50840, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42116 (p : Pattern) (guard : d348131 p = 1) : d50840 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259292 p = 1 := by simpa only [d348131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42115 p hg
    simpa only [d348131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41244 p hg
    simpa only [d348131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42117 (p : Pattern) (guard : d348132 p = 1) : d50881 p ≤ (1 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348131 p = 1 := by simpa only [d348132, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42116 p hg
    simpa only [d348132, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348132, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41246 p hg
    simpa only [d348132, d50881, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42118 (p : Pattern) (guard : d348133 p = 1) : d50884 p ≤ (1 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348132 p = 1 := by simpa only [d348133, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42117 p hg
    simpa only [d348133, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348133, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41248 p hg
    simpa only [d348133, d50884, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42119 (p : Pattern) (guard : d348134 p = 1) : d50907 p ≤ (1 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348134, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41227 p hg
    simpa only [d348134, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348133 p = 1 := by simpa only [d348134, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42118 p hg
    simpa only [d348134, d50907, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42120 (p : Pattern) (guard : d348135 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d348134 p = 1 := by simpa only [d348135, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42119 p hg
    simpa only [d348135, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348135, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41251 p hg
    simpa only [d348135, d50911, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42121 (p : Pattern) (guard : d348138 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d348135 p = 1 := by simpa only [d348138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42120 p hg
    simpa only [d348138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41226 p hg
    simpa only [d348138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42122 (p : Pattern) (guard : d348859 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41226 p hg
    simpa only [d348859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348138 p = 1 := by simpa only [d348859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42121 p hg
    simpa only [d348859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42123 (p : Pattern) (guard : d348143 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d348138 p = 1 := by simpa only [d348143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42121 p hg
    simpa only [d348143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41226 p hg
    simpa only [d348143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42124 (p : Pattern) (guard : d348860 p = 1) : d50911 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348859 p = 1 := by simpa only [d348860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42122 p hg
    simpa only [d348860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348143 p = 1 := by simpa only [d348860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42123 p hg
    simpa only [d348860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42125 (p : Pattern) (guard : d348861 p = 1) : d50912 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348861, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41225 p hg
    simpa only [d348861, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348860 p = 1 := by simpa only [d348861, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42124 p hg
    simpa only [d348861, d50912, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42126 (p : Pattern) (guard : d348862 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348862, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41224 p hg
    simpa only [d348862, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348861 p = 1 := by simpa only [d348862, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42125 p hg
    simpa only [d348862, d50952, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42127 (p : Pattern) (guard : d348863 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348862 p = 1 := by simpa only [d348863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42126 p hg
    simpa only [d348863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41264 p hg
    simpa only [d348863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42128 (p : Pattern) (guard : d348864 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41264 p hg
    simpa only [d348864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348863 p = 1 := by simpa only [d348864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42127 p hg
    simpa only [d348864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42129 (p : Pattern) (guard : d348865 p = 1) : d50952 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348864 p = 1 := by simpa only [d348865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42128 p hg
    simpa only [d348865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41264 p hg
    simpa only [d348865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42130 (p : Pattern) (guard : d348866 p = 1) : d50953 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348865 p = 1 := by simpa only [d348866, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42129 p hg
    simpa only [d348866, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348866, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41268 p hg
    simpa only [d348866, d50953, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42131 (p : Pattern) (guard : d348867 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348867, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41223 p hg
    simpa only [d348867, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348866 p = 1 := by simpa only [d348867, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42130 p hg
    simpa only [d348867, d50954, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42132 (p : Pattern) (guard : d348868 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348867 p = 1 := by simpa only [d348868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42131 p hg
    simpa only [d348868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42133 (p : Pattern) (guard : d348869 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348868 p = 1 := by simpa only [d348869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42132 p hg
    simpa only [d348869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42134 (p : Pattern) (guard : d348870 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348869 p = 1 := by simpa only [d348870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42133 p hg
    simpa only [d348870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42135 (p : Pattern) (guard : d348871 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348870 p = 1 := by simpa only [d348871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42134 p hg
    simpa only [d348871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42136 (p : Pattern) (guard : d348872 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348871 p = 1 := by simpa only [d348872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42135 p hg
    simpa only [d348872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42137 (p : Pattern) (guard : d348873 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348872 p = 1 := by simpa only [d348873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42136 p hg
    simpa only [d348873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42138 (p : Pattern) (guard : d348874 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348873 p = 1 := by simpa only [d348874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42137 p hg
    simpa only [d348874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42139 (p : Pattern) (guard : d348875 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348874 p = 1 := by simpa only [d348875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42138 p hg
    simpa only [d348875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42140 (p : Pattern) (guard : d348876 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348875 p = 1 := by simpa only [d348876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42139 p hg
    simpa only [d348876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42141 (p : Pattern) (guard : d348877 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348877, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348877, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348876 p = 1 := by simpa only [d348877, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42140 p hg
    simpa only [d348877, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42142 (p : Pattern) (guard : d348862 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348862, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41292 p hg
    simpa only [d348862, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348861 p = 1 := by simpa only [d348862, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42125 p hg
    simpa only [d348862, d50930, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42143 (p : Pattern) (guard : d348863 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348862 p = 1 := by simpa only [d348863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42142 p hg
    simpa only [d348863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41296 p hg
    simpa only [d348863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42144 (p : Pattern) (guard : d348864 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41296 p hg
    simpa only [d348864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348863 p = 1 := by simpa only [d348864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42143 p hg
    simpa only [d348864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42145 (p : Pattern) (guard : d348865 p = 1) : d50930 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348864 p = 1 := by simpa only [d348865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42144 p hg
    simpa only [d348865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41296 p hg
    simpa only [d348865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42146 (p : Pattern) (guard : d348866 p = 1) : d50932 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348865 p = 1 := by simpa only [d348866, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42145 p hg
    simpa only [d348866, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348866, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41268 p hg
    simpa only [d348866, d50932, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42147 (p : Pattern) (guard : d348867 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348867, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41291 p hg
    simpa only [d348867, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348866 p = 1 := by simpa only [d348867, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42146 p hg
    simpa only [d348867, d50933, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42148 (p : Pattern) (guard : d348868 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348867 p = 1 := by simpa only [d348868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42147 p hg
    simpa only [d348868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42149 (p : Pattern) (guard : d348869 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348868 p = 1 := by simpa only [d348869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42148 p hg
    simpa only [d348869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42150 (p : Pattern) (guard : d348870 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348869 p = 1 := by simpa only [d348870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42149 p hg
    simpa only [d348870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42151 (p : Pattern) (guard : d348871 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348870 p = 1 := by simpa only [d348871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42150 p hg
    simpa only [d348871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42152 (p : Pattern) (guard : d348872 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348871 p = 1 := by simpa only [d348872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42151 p hg
    simpa only [d348872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42153 (p : Pattern) (guard : d348873 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348872 p = 1 := by simpa only [d348873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42152 p hg
    simpa only [d348873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42154 (p : Pattern) (guard : d348874 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348873 p = 1 := by simpa only [d348874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42153 p hg
    simpa only [d348874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42155 (p : Pattern) (guard : d348875 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348874 p = 1 := by simpa only [d348875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42154 p hg
    simpa only [d348875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42156 (p : Pattern) (guard : d348876 p = 1) : d50933 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348875 p = 1 := by simpa only [d348876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42155 p hg
    simpa only [d348876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42157 (p : Pattern) (guard : d348878 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348870 p = 1 := by simpa only [d348878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42134 p hg
    simpa only [d348878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42158 (p : Pattern) (guard : d348879 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348878 p = 1 := by simpa only [d348879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42157 p hg
    simpa only [d348879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42159 (p : Pattern) (guard : d348880 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348879 p = 1 := by simpa only [d348880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42158 p hg
    simpa only [d348880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42160 (p : Pattern) (guard : d348881 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348880 p = 1 := by simpa only [d348881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42159 p hg
    simpa only [d348881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42161 (p : Pattern) (guard : d348882 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348881 p = 1 := by simpa only [d348882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42160 p hg
    simpa only [d348882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42162 (p : Pattern) (guard : d348883 p = 1) : d50954 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41222 p hg
    simpa only [d348883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348882 p = 1 := by simpa only [d348883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42161 p hg
    simpa only [d348883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42163 (p : Pattern) (guard : d348884 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d348876 p = 1 := by simpa only [d348884, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42156 p hg
    simpa only [d348884, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348883 p = 1 := by simpa only [d348884, d50955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42162 p hg
    simpa only [d348884, d50955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42164 (p : Pattern) (guard : d348885 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d348877 p = 1 := by simpa only [d348885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42141 p hg
    simpa only [d348885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348884 p = 1 := by simpa only [d348885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42163 p hg
    simpa only [d348885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42165 (p : Pattern) (guard : d348886 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d348885 p = 1 := by simpa only [d348886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42164 p hg
    simpa only [d348886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41220 p hg
    simpa only [d348886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42166 (p : Pattern) (guard : d348887 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d348886 p = 1 := by simpa only [d348887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42165 p hg
    simpa only [d348887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41220 p hg
    simpa only [d348887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42167 (p : Pattern) (guard : d348888 p = 1) : d50955 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41220 p hg
    simpa only [d348888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348887 p = 1 := by simpa only [d348888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42166 p hg
    simpa only [d348888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42168 (p : Pattern) (guard : d307 p = 1) : d5 p ≤ (1 : Int) + d5 p := by
  omega
theorem compare42169 (p : Pattern) (guard : d1997 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42168 p hg
    simpa only [d1997, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41466 p hg
    simpa only [d1997, d50965, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42170 (p : Pattern) (guard : d1998 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42169 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42171 (p : Pattern) (guard : d2013 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42169 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42172 (p : Pattern) (guard : d2014 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42170 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42171 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42173 (p : Pattern) (guard : d257871 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42172 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42174 (p : Pattern) (guard : d257872 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42173 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42175 (p : Pattern) (guard : d257873 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257872 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42174 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42176 (p : Pattern) (guard : d257874 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257873 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42175 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42177 (p : Pattern) (guard : d259291 p = 1) : d50965 p ≤ (1 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42176 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41464 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42178 (p : Pattern) (guard : d259292 p = 1) : d50967 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259291 p = 1 := by simpa only [d259292, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42177 p hg
    simpa only [d259292, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259292, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41478 p hg
    simpa only [d259292, d50967, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42179 (p : Pattern) (guard : d348131 p = 1) : d50967 p ≤ (1 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259292 p = 1 := by simpa only [d348131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42178 p hg
    simpa only [d348131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41480 p hg
    simpa only [d348131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42180 (p : Pattern) (guard : d348132 p = 1) : d50997 p ≤ (1 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348131 p = 1 := by simpa only [d348132, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42179 p hg
    simpa only [d348132, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348132, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41482 p hg
    simpa only [d348132, d50997, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42181 (p : Pattern) (guard : d348133 p = 1) : d50998 p ≤ (1 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348132 p = 1 := by simpa only [d348133, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42180 p hg
    simpa only [d348133, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348133, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d348133, d50998, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42182 (p : Pattern) (guard : d348134 p = 1) : d51018 p ≤ (1 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348134, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41463 p hg
    simpa only [d348134, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348133 p = 1 := by simpa only [d348134, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42181 p hg
    simpa only [d348134, d51018, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42183 (p : Pattern) (guard : d348135 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d348134 p = 1 := by simpa only [d348135, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42182 p hg
    simpa only [d348135, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348135, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41486 p hg
    simpa only [d348135, d51022, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42184 (p : Pattern) (guard : d348138 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d348135 p = 1 := by simpa only [d348138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42183 p hg
    simpa only [d348138, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348138, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41462 p hg
    simpa only [d348138, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42185 (p : Pattern) (guard : d348859 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41462 p hg
    simpa only [d348859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348138 p = 1 := by simpa only [d348859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42184 p hg
    simpa only [d348859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42186 (p : Pattern) (guard : d348143 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d348138 p = 1 := by simpa only [d348143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42184 p hg
    simpa only [d348143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41462 p hg
    simpa only [d348143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42187 (p : Pattern) (guard : d348860 p = 1) : d51022 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348859 p = 1 := by simpa only [d348860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42185 p hg
    simpa only [d348860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348143 p = 1 := by simpa only [d348860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42186 p hg
    simpa only [d348860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42188 (p : Pattern) (guard : d348861 p = 1) : d51023 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348861, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41461 p hg
    simpa only [d348861, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348860 p = 1 := by simpa only [d348861, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42187 p hg
    simpa only [d348861, d51023, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42189 (p : Pattern) (guard : d348862 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348862, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41460 p hg
    simpa only [d348862, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348861 p = 1 := by simpa only [d348862, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42188 p hg
    simpa only [d348862, d51034, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42190 (p : Pattern) (guard : d348863 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348862 p = 1 := by simpa only [d348863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42189 p hg
    simpa only [d348863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41508 p hg
    simpa only [d348863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42191 (p : Pattern) (guard : d348864 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41508 p hg
    simpa only [d348864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348863 p = 1 := by simpa only [d348864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42190 p hg
    simpa only [d348864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42192 (p : Pattern) (guard : d348865 p = 1) : d51034 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348864 p = 1 := by simpa only [d348865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42191 p hg
    simpa only [d348865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41508 p hg
    simpa only [d348865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42193 (p : Pattern) (guard : d348866 p = 1) : d51036 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d348865 p = 1 := by simpa only [d348866, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42192 p hg
    simpa only [d348866, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348866, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41510 p hg
    simpa only [d348866, d51036, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42194 (p : Pattern) (guard : d348867 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348867, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41459 p hg
    simpa only [d348867, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348866 p = 1 := by simpa only [d348867, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42193 p hg
    simpa only [d348867, d51037, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42195 (p : Pattern) (guard : d348868 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d348867 p = 1 := by simpa only [d348868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42194 p hg
    simpa only [d348868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42196 (p : Pattern) (guard : d348869 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d348868 p = 1 := by simpa only [d348869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42195 p hg
    simpa only [d348869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42197 (p : Pattern) (guard : d348870 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d348869 p = 1 := by simpa only [d348870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42196 p hg
    simpa only [d348870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42198 (p : Pattern) (guard : d348878 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d348870 p = 1 := by simpa only [d348878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42197 p hg
    simpa only [d348878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42199 (p : Pattern) (guard : d348879 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d348878 p = 1 := by simpa only [d348879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42198 p hg
    simpa only [d348879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42200 (p : Pattern) (guard : d348880 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d348879 p = 1 := by simpa only [d348880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42199 p hg
    simpa only [d348880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42201 (p : Pattern) (guard : d348881 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348880 p = 1 := by simpa only [d348881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42200 p hg
    simpa only [d348881, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42202 (p : Pattern) (guard : d348882 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348881 p = 1 := by simpa only [d348882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42201 p hg
    simpa only [d348882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42203 (p : Pattern) (guard : d348883 p = 1) : d51037 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41458 p hg
    simpa only [d348883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348882 p = 1 := by simpa only [d348883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42202 p hg
    simpa only [d348883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42204 (p : Pattern) (guard : d348889 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348889, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41221 p hg
    simpa only [d348889, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348883 p = 1 := by simpa only [d348889, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42203 p hg
    simpa only [d348889, d51038, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42205 (p : Pattern) (guard : d348890 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41457 p hg
    simpa only [d348890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348889 p = 1 := by simpa only [d348890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42204 p hg
    simpa only [d348890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42206 (p : Pattern) (guard : d348891 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d348890 p = 1 := by simpa only [d348891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42205 p hg
    simpa only [d348891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41457 p hg
    simpa only [d348891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42207 (p : Pattern) (guard : d348892 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d348891 p = 1 := by simpa only [d348892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42206 p hg
    simpa only [d348892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41457 p hg
    simpa only [d348892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42208 (p : Pattern) (guard : d348893 p = 1) : d51038 p ≤ (1 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d348892 p = 1 := by simpa only [d348893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42207 p hg
    simpa only [d348893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41457 p hg
    simpa only [d348893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42209 (p : Pattern) (guard : d348894 p = 1) : d51039 p ≤ (1 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d348888 p = 1 := by simpa only [d348894, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42167 p hg
    simpa only [d348894, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348893 p = 1 := by simpa only [d348894, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42208 p hg
    simpa only [d348894, d51039, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42210 (p : Pattern) (guard : d307 p = 1) : d2 p ≤ (1 : Int) + d2 p := by
  omega
theorem compare42211 (p : Pattern) (guard : d1997 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42210 p hg
    simpa only [d1997, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41566 p hg
    simpa only [d1997, d50849, d47630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42212 (p : Pattern) (guard : d1998 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42211 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42213 (p : Pattern) (guard : d2013 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42211 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42214 (p : Pattern) (guard : d2014 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42212 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42213 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42215 (p : Pattern) (guard : d257871 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42214 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42216 (p : Pattern) (guard : d257872 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42215 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42217 (p : Pattern) (guard : d257873 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257872 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42216 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42218 (p : Pattern) (guard : d257874 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257873 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42217 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42219 (p : Pattern) (guard : d259291 p = 1) : d50849 p ≤ (1 : Int) + d47630 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42218 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41564 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42220 (p : Pattern) (guard : d259292 p = 1) : d50874 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259291 p = 1 := by simpa only [d259292, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42219 p hg
    simpa only [d259292, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259292, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41578 p hg
    simpa only [d259292, d50874, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42221 (p : Pattern) (guard : d348131 p = 1) : d50874 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259292 p = 1 := by simpa only [d348131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42220 p hg
    simpa only [d348131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41563 p hg
    simpa only [d348131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42222 (p : Pattern) (guard : d348276 p = 1) : d50874 p ≤ (1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41563 p hg
    simpa only [d348276, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348131 p = 1 := by simpa only [d348276, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42221 p hg
    simpa only [d348276, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42223 (p : Pattern) (guard : d348132 p = 1) : d51067 p ≤ (1 : Int) + d47797 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348131 p = 1 := by simpa only [d348132, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42116 p hg
    simpa only [d348132, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348132, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41482 p hg
    simpa only [d348132, d51067, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42224 (p : Pattern) (guard : d348277 p = 1) : d51068 p ≤ (1 : Int) + d47798 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348276 p = 1 := by simpa only [d348277, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42222 p hg
    simpa only [d348277, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348132 p = 1 := by simpa only [d348277, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42223 p hg
    simpa only [d348277, d51068, d47798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42225 (p : Pattern) (guard : d307 p = 1) : d6 p ≤ (1 : Int) + d6 p := by
  omega
theorem compare42226 (p : Pattern) (guard : d1997 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42225 p hg
    simpa only [d1997, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41586 p hg
    simpa only [d1997, d50852, d47634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42227 (p : Pattern) (guard : d1998 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42226 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42228 (p : Pattern) (guard : d2013 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42226 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42229 (p : Pattern) (guard : d2014 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42227 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42228 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42230 (p : Pattern) (guard : d257871 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42229 p hg
    simpa only [d257871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42231 (p : Pattern) (guard : d257872 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42230 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d257872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42232 (p : Pattern) (guard : d257873 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257872 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42231 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d257873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42233 (p : Pattern) (guard : d257874 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257873 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42232 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d257874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42234 (p : Pattern) (guard : d259291 p = 1) : d50852 p ≤ (1 : Int) + d47634 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257874 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42233 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41584 p hg
    simpa only [d259291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42235 (p : Pattern) (guard : d259292 p = 1) : d50900 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259291 p = 1 := by simpa only [d259292, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42234 p hg
    simpa only [d259292, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259292, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41598 p hg
    simpa only [d259292, d50900, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42236 (p : Pattern) (guard : d348131 p = 1) : d50900 p ≤ (1 : Int) + d47677 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259292 p = 1 := by simpa only [d348131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42235 p hg
    simpa only [d348131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41600 p hg
    simpa only [d348131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42237 (p : Pattern) (guard : d348132 p = 1) : d50908 p ≤ (1 : Int) + d47682 p := by
  cases selected : p 163 with
  | false =>
    have hg : d348131 p = 1 := by simpa only [d348132, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42236 p hg
    simpa only [d348132, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348132, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d348132, d50908, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42238 (p : Pattern) (guard : d348133 p = 1) : d50909 p ≤ (1 : Int) + d47683 p := by
  cases selected : p 162 with
  | false =>
    have hg : d348132 p = 1 := by simpa only [d348133, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42237 p hg
    simpa only [d348133, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348133, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare32065 p hg
    simpa only [d348133, d50909, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42239 (p : Pattern) (guard : d348278 p = 1) : d51069 p ≤ (1 : Int) + d47799 p := by
  cases selected : p 161 with
  | false =>
    have hg : d348277 p = 1 := by simpa only [d348278, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42224 p hg
    simpa only [d348278, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348133 p = 1 := by simpa only [d348278, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42238 p hg
    simpa only [d348278, d51069, d47799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42240 (p : Pattern) (guard : d348279 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d348278 p = 1 := by simpa only [d348279, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42239 p hg
    simpa only [d348279, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348279, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41605 p hg
    simpa only [d348279, d51073, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42241 (p : Pattern) (guard : d348285 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d348279 p = 1 := by simpa only [d348285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42240 p hg
    simpa only [d348285, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348285, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41562 p hg
    simpa only [d348285, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42242 (p : Pattern) (guard : d348895 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41562 p hg
    simpa only [d348895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348285 p = 1 := by simpa only [d348895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42241 p hg
    simpa only [d348895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42243 (p : Pattern) (guard : d348291 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d348285 p = 1 := by simpa only [d348291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42241 p hg
    simpa only [d348291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41562 p hg
    simpa only [d348291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42244 (p : Pattern) (guard : d348896 p = 1) : d51073 p ≤ (1 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d348895 p = 1 := by simpa only [d348896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42242 p hg
    simpa only [d348896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348291 p = 1 := by simpa only [d348896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42243 p hg
    simpa only [d348896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42245 (p : Pattern) (guard : d348897 p = 1) : d51074 p ≤ (1 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348897, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41561 p hg
    simpa only [d348897, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348896 p = 1 := by simpa only [d348897, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42244 p hg
    simpa only [d348897, d51074, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42246 (p : Pattern) (guard : d348898 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348898, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41560 p hg
    simpa only [d348898, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348897 p = 1 := by simpa only [d348898, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42245 p hg
    simpa only [d348898, d51075, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42247 (p : Pattern) (guard : d348899 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d348898 p = 1 := by simpa only [d348899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42246 p hg
    simpa only [d348899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41627 p hg
    simpa only [d348899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42248 (p : Pattern) (guard : d348900 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d348900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41627 p hg
    simpa only [d348900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d348899 p = 1 := by simpa only [d348900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42247 p hg
    simpa only [d348900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare42249 (p : Pattern) (guard : d348901 p = 1) : d51075 p ≤ (1 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d348900 p = 1 := by simpa only [d348901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare42248 p hg
    simpa only [d348901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d348901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41627 p hg
    simpa only [d348901, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
