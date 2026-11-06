import NetHack.Soko22Hazard87.Compare022
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare5750 (p : Pattern) (guard : d1005 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1004 p = 1 := by simpa only [d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5749 p hg
    simpa only [d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5751 (p : Pattern) (guard : d1006 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1005 p = 1 := by simpa only [d1006, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5750 p hg
    simpa only [d1006, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1006, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d1006, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5752 (p : Pattern) (guard : d1007 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1007, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d1007, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1006 p = 1 := by simpa only [d1007, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5751 p hg
    simpa only [d1007, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5753 (p : Pattern) (guard : d6930 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d6218 p = 1 := by simpa only [d6930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5747 p hg
    simpa only [d6930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1007 p = 1 := by simpa only [d6930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5752 p hg
    simpa only [d6930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5754 (p : Pattern) (guard : d6931 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6930 p = 1 := by simpa only [d6931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5753 p hg
    simpa only [d6931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5755 (p : Pattern) (guard : d6932 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6931 p = 1 := by simpa only [d6932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5754 p hg
    simpa only [d6932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5756 (p : Pattern) (guard : d6933 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6932 p = 1 := by simpa only [d6933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5755 p hg
    simpa only [d6933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5757 (p : Pattern) (guard : d6934 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6929 p = 1 := by simpa only [d6934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5743 p hg
    simpa only [d6934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6933 p = 1 := by simpa only [d6934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5756 p hg
    simpa only [d6934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5758 (p : Pattern) (guard : d82129 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6934 p = 1 := by simpa only [d82129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5757 p hg
    simpa only [d82129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5759 (p : Pattern) (guard : d996 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d990 p = 1 := by simpa only [d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5725 p hg
    simpa only [d996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d995 p = 1 := by simpa only [d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5748 p hg
    simpa only [d996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5760 (p : Pattern) (guard : d997 p = 1) : d47805 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d996 p = 1 := by simpa only [d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5759 p hg
    simpa only [d997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4564 p hg
    simpa only [d997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5761 (p : Pattern) (guard : d998 p = 1) : d47807 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d997 p = 1 := by simpa only [d998, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5760 p hg
    simpa only [d998, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d998, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4568 p hg
    simpa only [d998, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5762 (p : Pattern) (guard : d999 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d999, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d999, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d998 p = 1 := by simpa only [d999, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5761 p hg
    simpa only [d999, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5763 (p : Pattern) (guard : d6230 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d999 p = 1 := by simpa only [d6230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5762 p hg
    simpa only [d6230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5764 (p : Pattern) (guard : d6231 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6230 p = 1 := by simpa only [d6231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5763 p hg
    simpa only [d6231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5765 (p : Pattern) (guard : d6232 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6231 p = 1 := by simpa only [d6232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5764 p hg
    simpa only [d6232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5766 (p : Pattern) (guard : d6233 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6232 p = 1 := by simpa only [d6233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5765 p hg
    simpa only [d6233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5767 (p : Pattern) (guard : d6234 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6233 p = 1 := by simpa only [d6234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5766 p hg
    simpa only [d6234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5768 (p : Pattern) (guard : d6235 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6234 p = 1 := by simpa only [d6235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5767 p hg
    simpa only [d6235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d6235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5769 (p : Pattern) (guard : d82130 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82129 p = 1 := by simpa only [d82130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5758 p hg
    simpa only [d82130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6235 p = 1 := by simpa only [d82130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5768 p hg
    simpa only [d82130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5770 (p : Pattern) (guard : d82131 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82130 p = 1 := by simpa only [d82131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5769 p hg
    simpa only [d82131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5771 (p : Pattern) (guard : d82132 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d82132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82131 p = 1 := by simpa only [d82132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5770 p hg
    simpa only [d82132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5772 (p : Pattern) (guard : d82133 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82133, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82133, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82132 p = 1 := by simpa only [d82133, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5771 p hg
    simpa only [d82133, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5773 (p : Pattern) (guard : d82134 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82133 p = 1 := by simpa only [d82134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5772 p hg
    simpa only [d82134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5774 (p : Pattern) (guard : d1060 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1007 p = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5752 p hg
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5775 (p : Pattern) (guard : d1061 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1060 p = 1 := by simpa only [d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5774 p hg
    simpa only [d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5776 (p : Pattern) (guard : d1062 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1061 p = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5775 p hg
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5777 (p : Pattern) (guard : d1063 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1062 p = 1 := by simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5776 p hg
    simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5778 (p : Pattern) (guard : d1064 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1063 p = 1 := by simpa only [d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5777 p hg
    simpa only [d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5779 (p : Pattern) (guard : d1065 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1064 p = 1 := by simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5778 p hg
    simpa only [d1065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5780 (p : Pattern) (guard : d1066 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1065 p = 1 := by simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5779 p hg
    simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5781 (p : Pattern) (guard : d1067 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1066 p = 1 := by simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5780 p hg
    simpa only [d1067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5782 (p : Pattern) (guard : d1068 p = 1) : d47808 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4516 p hg
    simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1067 p = 1 := by simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5781 p hg
    simpa only [d1068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5783 (p : Pattern) (guard : d1069 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1069, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1069, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1068 p = 1 := by simpa only [d1069, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5782 p hg
    simpa only [d1069, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5784 (p : Pattern) (guard : d1070 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1069 p = 1 := by simpa only [d1070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5783 p hg
    simpa only [d1070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5785 (p : Pattern) (guard : d82135 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d82134 p = 1 := by simpa only [d82135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5773 p hg
    simpa only [d82135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1070 p = 1 := by simpa only [d82135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5784 p hg
    simpa only [d82135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5786 (p : Pattern) (guard : d82136 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d82135 p = 1 := by simpa only [d82136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5785 p hg
    simpa only [d82136, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82136, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82136, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5787 (p : Pattern) (guard : d82137 p = 1) : d47809 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d82136 p = 1 := by simpa only [d82137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5786 p hg
    simpa only [d82137, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82137, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4515 p hg
    simpa only [d82137, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5788 (p : Pattern) (guard : d82138 p = 1) : d47865 p ≤ (-1 : Int) + d98795 p := by
  cases selected : p 49 with
  | false =>
    have hg : d82137 p = 1 := by simpa only [d82138, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5787 p hg
    simpa only [d82138, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82138, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4585 p hg
    simpa only [d82138, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5789 (p : Pattern) (guard : d82139 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 48 with
  | false =>
    have hg : d82128 p = 1 := by simpa only [d82139, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5663 p hg
    simpa only [d82139, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82138 p = 1 := by simpa only [d82139, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5788 p hg
    simpa only [d82139, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5790 (p : Pattern) (guard : d82140 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82139 p = 1 := by simpa only [d82140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5789 p hg
    simpa only [d82140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5791 (p : Pattern) (guard : d82141 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82140 p = 1 := by simpa only [d82141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5790 p hg
    simpa only [d82141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5792 (p : Pattern) (guard : d82142 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82141 p = 1 := by simpa only [d82142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5791 p hg
    simpa only [d82142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5793 (p : Pattern) (guard : d82143 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82142 p = 1 := by simpa only [d82143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5792 p hg
    simpa only [d82143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5794 (p : Pattern) (guard : d82144 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82144, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82143 p = 1 := by simpa only [d82144, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5793 p hg
    simpa only [d82144, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5795 (p : Pattern) (guard : d82145 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82144 p = 1 := by simpa only [d82145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5794 p hg
    simpa only [d82145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5796 (p : Pattern) (guard : d82146 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4399 p hg
    simpa only [d82146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82145 p = 1 := by simpa only [d82146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5795 p hg
    simpa only [d82146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5797 (p : Pattern) (guard : d82147 p = 1) : d47866 p ≤ (-1 : Int) + d98796 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d82106 p = 1 := by simpa only [d82147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5383 p hg
    simpa only [d82147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82146 p = 1 := by simpa only [d82147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5796 p hg
    simpa only [d82147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5798 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (-1 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare5799 (p : Pattern) (guard : d1084 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5798 p hg
    simpa only [d1084, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4621 p hg
    simpa only [d1084, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5800 (p : Pattern) (guard : d1085 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5799 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5801 (p : Pattern) (guard : d1086 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5800 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5802 (p : Pattern) (guard : d1087 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5801 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5803 (p : Pattern) (guard : d1088 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5079 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5802 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5804 (p : Pattern) (guard : d1089 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5803 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5805 (p : Pattern) (guard : d1090 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5457 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1089 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5804 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5806 (p : Pattern) (guard : d1091 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1090 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5805 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5464 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5807 (p : Pattern) (guard : d1092 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1091 p = 1 := by simpa only [d1092, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5806 p hg
    simpa only [d1092, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d1092, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5808 (p : Pattern) (guard : d1093 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5801 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4410 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5809 (p : Pattern) (guard : d1094 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4817 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5808 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5810 (p : Pattern) (guard : d1095 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5809 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5811 (p : Pattern) (guard : d1096 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5804 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5810 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5812 (p : Pattern) (guard : d1097 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5811 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5088 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5813 (p : Pattern) (guard : d1098 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1097 p = 1 := by simpa only [d1098, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5812 p hg
    simpa only [d1098, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1098, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d1098, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5814 (p : Pattern) (guard : d1099 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5807 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1098 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5813 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5815 (p : Pattern) (guard : d1100 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5814 p hg
    simpa only [d1100, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d1100, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5816 (p : Pattern) (guard : d1101 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1100 p = 1 := by simpa only [d1101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5815 p hg
    simpa only [d1101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5817 (p : Pattern) (guard : d1102 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1102, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d1102, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1102, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5816 p hg
    simpa only [d1102, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5818 (p : Pattern) (guard : d1103 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5817 p hg
    simpa only [d1103, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d1103, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5819 (p : Pattern) (guard : d1104 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4625 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4411 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5820 (p : Pattern) (guard : d1105 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1104 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5819 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5821 (p : Pattern) (guard : d1106 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5810 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1105 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5820 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5822 (p : Pattern) (guard : d1107 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1106 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5821 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4628 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5823 (p : Pattern) (guard : d1108 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1107 p = 1 := by simpa only [d1108, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5822 p hg
    simpa only [d1108, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1108, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d1108, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5824 (p : Pattern) (guard : d1109 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5813 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1108 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5823 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5825 (p : Pattern) (guard : d1110 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5824 p hg
    simpa only [d1110, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d1110, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5826 (p : Pattern) (guard : d1111 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1110 p = 1 := by simpa only [d1111, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5825 p hg
    simpa only [d1111, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1111, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1111, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5827 (p : Pattern) (guard : d1112 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d1112, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5826 p hg
    simpa only [d1112, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5828 (p : Pattern) (guard : d1113 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5827 p hg
    simpa only [d1113, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d1113, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5829 (p : Pattern) (guard : d1114 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5818 p hg
    simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1113 p = 1 := by simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5828 p hg
    simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5830 (p : Pattern) (guard : d1115 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4411 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5831 (p : Pattern) (guard : d1116 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1115 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5830 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5832 (p : Pattern) (guard : d1117 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5831 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4413 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5833 (p : Pattern) (guard : d1118 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1117 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5832 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4414 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5834 (p : Pattern) (guard : d1119 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1118 p = 1 := by simpa only [d1119, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5833 p hg
    simpa only [d1119, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1119, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d1119, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5835 (p : Pattern) (guard : d1120 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1108 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5823 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5834 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5836 (p : Pattern) (guard : d1121 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5835 p hg
    simpa only [d1121, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d1121, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5837 (p : Pattern) (guard : d1122 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1121 p = 1 := by simpa only [d1122, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5836 p hg
    simpa only [d1122, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1122, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5838 (p : Pattern) (guard : d1123 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d1123, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5837 p hg
    simpa only [d1123, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5839 (p : Pattern) (guard : d1124 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5838 p hg
    simpa only [d1124, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d1124, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5840 (p : Pattern) (guard : d1125 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5828 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5839 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5841 (p : Pattern) (guard : d1126 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1114 p = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5829 p hg
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1125 p = 1 := by simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5840 p hg
    simpa only [d1126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5842 (p : Pattern) (guard : d1127 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1124 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5839 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d1127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5843 (p : Pattern) (guard : d1128 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5840 p hg
    simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1127 p = 1 := by simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5842 p hg
    simpa only [d1128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5844 (p : Pattern) (guard : d1129 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1126 p = 1 := by simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5841 p hg
    simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1128 p = 1 := by simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5843 p hg
    simpa only [d1129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5845 (p : Pattern) (guard : d1130 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1130, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d1130, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1129 p = 1 := by simpa only [d1130, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5844 p hg
    simpa only [d1130, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5846 (p : Pattern) (guard : d1131 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1131, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d1131, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1130 p = 1 := by simpa only [d1131, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5845 p hg
    simpa only [d1131, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5847 (p : Pattern) (guard : d1132 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5831 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5848 (p : Pattern) (guard : d1133 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5847 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5849 (p : Pattern) (guard : d1134 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1133 p = 1 := by simpa only [d1134, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5848 p hg
    simpa only [d1134, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1134, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d1134, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5850 (p : Pattern) (guard : d1135 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1134 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5849 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4418 p hg
    simpa only [d1135, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5851 (p : Pattern) (guard : d1136 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1135 p = 1 := by simpa only [d1136, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5850 p hg
    simpa only [d1136, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1136, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d1136, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5852 (p : Pattern) (guard : d1137 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1136 p = 1 := by simpa only [d1137, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5851 p hg
    simpa only [d1137, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1137, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1137, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5853 (p : Pattern) (guard : d1138 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1138, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d1138, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1137 p = 1 := by simpa only [d1138, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5852 p hg
    simpa only [d1138, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5854 (p : Pattern) (guard : d1139 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1138 p = 1 := by simpa only [d1139, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5853 p hg
    simpa only [d1139, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1139, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d1139, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5855 (p : Pattern) (guard : d1140 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1139 p = 1 := by simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5854 p hg
    simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d1140, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5856 (p : Pattern) (guard : d1141 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1127 p = 1 := by simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5842 p hg
    simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1140 p = 1 := by simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5855 p hg
    simpa only [d1141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5857 (p : Pattern) (guard : d1142 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1128 p = 1 := by simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5843 p hg
    simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1141 p = 1 := by simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5856 p hg
    simpa only [d1142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5858 (p : Pattern) (guard : d1143 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1143, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d1143, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1142 p = 1 := by simpa only [d1143, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5857 p hg
    simpa only [d1143, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5859 (p : Pattern) (guard : d1144 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1144, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d1144, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1143 p = 1 := by simpa only [d1144, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5858 p hg
    simpa only [d1144, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5860 (p : Pattern) (guard : d1145 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1131 p = 1 := by simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5846 p hg
    simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1144 p = 1 := by simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5859 p hg
    simpa only [d1145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5861 (p : Pattern) (guard : d1146 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1144 p = 1 := by simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5859 p hg
    simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d1146, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5862 (p : Pattern) (guard : d1147 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1145 p = 1 := by simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5860 p hg
    simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1146 p = 1 := by simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5861 p hg
    simpa only [d1147, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5863 (p : Pattern) (guard : d1148 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1147 p = 1 := by simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5862 p hg
    simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d1148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5864 (p : Pattern) (guard : d1149 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1148 p = 1 := by simpa only [d1149, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5863 p hg
    simpa only [d1149, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1149, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d1149, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5865 (p : Pattern) (guard : d1150 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1150, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d1150, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1149 p = 1 := by simpa only [d1150, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5864 p hg
    simpa only [d1150, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5866 (p : Pattern) (guard : d1151 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1146 p = 1 := by simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5861 p hg
    simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d1151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5867 (p : Pattern) (guard : d1152 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1151 p = 1 := by simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5866 p hg
    simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d1152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5868 (p : Pattern) (guard : d1153 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1152 p = 1 := by simpa only [d1153, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5867 p hg
    simpa only [d1153, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1153, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d1153, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5869 (p : Pattern) (guard : d1154 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1154, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d1154, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1153 p = 1 := by simpa only [d1154, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5868 p hg
    simpa only [d1154, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5870 (p : Pattern) (guard : d1155 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5865 p hg
    simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1154 p = 1 := by simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5869 p hg
    simpa only [d1155, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5871 (p : Pattern) (guard : d1156 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1155 p = 1 := by simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5870 p hg
    simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1156, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5872 (p : Pattern) (guard : d1157 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1156 p = 1 := by simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5871 p hg
    simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1157, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5873 (p : Pattern) (guard : d1158 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1157 p = 1 := by simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5872 p hg
    simpa only [d1158, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5874 (p : Pattern) (guard : d1159 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1154 p = 1 := by simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5869 p hg
    simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1159, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5875 (p : Pattern) (guard : d1160 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1159 p = 1 := by simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5874 p hg
    simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1160, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5876 (p : Pattern) (guard : d1161 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1160 p = 1 := by simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5875 p hg
    simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1161, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5877 (p : Pattern) (guard : d1162 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1161 p = 1 := by simpa only [d1162, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5876 p hg
    simpa only [d1162, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5878 (p : Pattern) (guard : d1163 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1158 p = 1 := by simpa only [d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5873 p hg
    simpa only [d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1162 p = 1 := by simpa only [d1163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5877 p hg
    simpa only [d1163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5879 (p : Pattern) (guard : d1164 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1163 p = 1 := by simpa only [d1164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5878 p hg
    simpa only [d1164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5880 (p : Pattern) (guard : d1165 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1164 p = 1 := by simpa only [d1165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5879 p hg
    simpa only [d1165, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1165, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1165, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5881 (p : Pattern) (guard : d1166 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1165 p = 1 := by simpa only [d1166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5880 p hg
    simpa only [d1166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5882 (p : Pattern) (guard : d1167 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1166 p = 1 := by simpa only [d1167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5881 p hg
    simpa only [d1167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5883 (p : Pattern) (guard : d1168 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1167 p = 1 := by simpa only [d1168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5882 p hg
    simpa only [d1168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5884 (p : Pattern) (guard : d1169 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1168 p = 1 := by simpa only [d1169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5883 p hg
    simpa only [d1169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5885 (p : Pattern) (guard : d1170 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d1169 p = 1 := by simpa only [d1170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5884 p hg
    simpa only [d1170, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1170, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1170, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5886 (p : Pattern) (guard : d1171 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1157 p = 1 := by simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5872 p hg
    simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5887 (p : Pattern) (guard : d1172 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1161 p = 1 := by simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5876 p hg
    simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5888 (p : Pattern) (guard : d1173 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1171 p = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5886 p hg
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1172 p = 1 := by simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5887 p hg
    simpa only [d1173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5889 (p : Pattern) (guard : d1174 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1173 p = 1 := by simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5888 p hg
    simpa only [d1174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5890 (p : Pattern) (guard : d1175 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1174 p = 1 := by simpa only [d1175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5889 p hg
    simpa only [d1175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5891 (p : Pattern) (guard : d1176 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1175 p = 1 := by simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5890 p hg
    simpa only [d1176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5892 (p : Pattern) (guard : d1177 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1176 p = 1 := by simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5891 p hg
    simpa only [d1177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5893 (p : Pattern) (guard : d1178 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d1167 p = 1 := by simpa only [d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5882 p hg
    simpa only [d1178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1177 p = 1 := by simpa only [d1178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5892 p hg
    simpa only [d1178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5894 (p : Pattern) (guard : d1179 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d1168 p = 1 := by simpa only [d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5883 p hg
    simpa only [d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1178 p = 1 := by simpa only [d1179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5893 p hg
    simpa only [d1179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5895 (p : Pattern) (guard : d1180 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d1179 p = 1 := by simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5894 p hg
    simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5896 (p : Pattern) (guard : d1181 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d1170 p = 1 := by simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5885 p hg
    simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1180 p = 1 := by simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5895 p hg
    simpa only [d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5897 (p : Pattern) (guard : d1182 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1156 p = 1 := by simpa only [d1182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5871 p hg
    simpa only [d1182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5898 (p : Pattern) (guard : d1183 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1182 p = 1 := by simpa only [d1183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5897 p hg
    simpa only [d1183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5899 (p : Pattern) (guard : d1184 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1160 p = 1 := by simpa only [d1184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5875 p hg
    simpa only [d1184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5900 (p : Pattern) (guard : d1185 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1184 p = 1 := by simpa only [d1185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5899 p hg
    simpa only [d1185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5901 (p : Pattern) (guard : d1186 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1183 p = 1 := by simpa only [d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5898 p hg
    simpa only [d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1185 p = 1 := by simpa only [d1186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5900 p hg
    simpa only [d1186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5902 (p : Pattern) (guard : d1187 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1186 p = 1 := by simpa only [d1187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5901 p hg
    simpa only [d1187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5903 (p : Pattern) (guard : d1188 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1187 p = 1 := by simpa only [d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5902 p hg
    simpa only [d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5904 (p : Pattern) (guard : d1189 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1188 p = 1 := by simpa only [d1189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5903 p hg
    simpa only [d1189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5905 (p : Pattern) (guard : d1190 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1155 p = 1 := by simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5870 p hg
    simpa only [d1190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5906 (p : Pattern) (guard : d1191 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1190 p = 1 := by simpa only [d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5905 p hg
    simpa only [d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5907 (p : Pattern) (guard : d1192 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1191 p = 1 := by simpa only [d1192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5906 p hg
    simpa only [d1192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5908 (p : Pattern) (guard : d1193 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1159 p = 1 := by simpa only [d1193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5874 p hg
    simpa only [d1193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5909 (p : Pattern) (guard : d1194 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1193 p = 1 := by simpa only [d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5908 p hg
    simpa only [d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5910 (p : Pattern) (guard : d1195 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1194 p = 1 := by simpa only [d1195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5909 p hg
    simpa only [d1195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5911 (p : Pattern) (guard : d1196 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1192 p = 1 := by simpa only [d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5907 p hg
    simpa only [d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1195 p = 1 := by simpa only [d1196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5910 p hg
    simpa only [d1196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5912 (p : Pattern) (guard : d1197 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1196 p = 1 := by simpa only [d1197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5911 p hg
    simpa only [d1197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5913 (p : Pattern) (guard : d1198 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1197 p = 1 := by simpa only [d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5912 p hg
    simpa only [d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5914 (p : Pattern) (guard : d1199 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5454 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5915 (p : Pattern) (guard : d1200 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1199 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5914 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5916 (p : Pattern) (guard : d1201 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1200 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5915 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5917 (p : Pattern) (guard : d1202 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5916 p hg
    simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d823 p = 1 := by simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5457 p hg
    simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5918 (p : Pattern) (guard : d1203 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5460 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5919 (p : Pattern) (guard : d1204 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1203 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5918 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5920 (p : Pattern) (guard : d1205 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1204 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5919 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5921 (p : Pattern) (guard : d1206 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5920 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5463 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5922 (p : Pattern) (guard : d1207 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1202 p = 1 := by simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5917 p hg
    simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1206 p = 1 := by simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5921 p hg
    simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5923 (p : Pattern) (guard : d1208 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1207 p = 1 := by simpa only [d1208, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5922 p hg
    simpa only [d1208, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1208, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d1208, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5924 (p : Pattern) (guard : d1209 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1208 p = 1 := by simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5923 p hg
    simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5807 p hg
    simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5925 (p : Pattern) (guard : d1210 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1209 p = 1 := by simpa only [d1210, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5924 p hg
    simpa only [d1210, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1210, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d1210, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5926 (p : Pattern) (guard : d1211 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1210 p = 1 := by simpa only [d1211, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5925 p hg
    simpa only [d1211, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1211, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d1211, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5927 (p : Pattern) (guard : d1212 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1212, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d1212, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1211 p = 1 := by simpa only [d1212, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5926 p hg
    simpa only [d1212, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5928 (p : Pattern) (guard : d1213 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1212 p = 1 := by simpa only [d1213, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5927 p hg
    simpa only [d1213, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1213, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d1213, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5929 (p : Pattern) (guard : d1214 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1213 p = 1 := by simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5928 p hg
    simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1103 p = 1 := by simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5818 p hg
    simpa only [d1214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5930 (p : Pattern) (guard : d1215 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1214 p = 1 := by simpa only [d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5929 p hg
    simpa only [d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1114 p = 1 := by simpa only [d1215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5829 p hg
    simpa only [d1215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5931 (p : Pattern) (guard : d1216 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d1215 p = 1 := by simpa only [d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5930 p hg
    simpa only [d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1126 p = 1 := by simpa only [d1216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5841 p hg
    simpa only [d1216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5932 (p : Pattern) (guard : d1217 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1217, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d1217, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1216 p = 1 := by simpa only [d1217, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5931 p hg
    simpa only [d1217, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5933 (p : Pattern) (guard : d1218 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1218, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d1218, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1217 p = 1 := by simpa only [d1218, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5932 p hg
    simpa only [d1218, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5934 (p : Pattern) (guard : d1219 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1218 p = 1 := by simpa only [d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5933 p hg
    simpa only [d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1131 p = 1 := by simpa only [d1219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5846 p hg
    simpa only [d1219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5935 (p : Pattern) (guard : d1220 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1219 p = 1 := by simpa only [d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5934 p hg
    simpa only [d1220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1145 p = 1 := by simpa only [d1220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5860 p hg
    simpa only [d1220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5936 (p : Pattern) (guard : d1221 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1220 p = 1 := by simpa only [d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5935 p hg
    simpa only [d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d1221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5937 (p : Pattern) (guard : d1222 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1221 p = 1 := by simpa only [d1222, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5936 p hg
    simpa only [d1222, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1222, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d1222, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5938 (p : Pattern) (guard : d1223 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1223, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d1223, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1222 p = 1 := by simpa only [d1223, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5937 p hg
    simpa only [d1223, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5939 (p : Pattern) (guard : d6954 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d1131 p = 1 := by simpa only [d6954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5846 p hg
    simpa only [d6954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d6954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5940 (p : Pattern) (guard : d5009 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d5009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5840 p hg
    simpa only [d5009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d5009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5941 (p : Pattern) (guard : d5010 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d534 p = 1 := by simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5083 p hg
    simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16 p = 1 := by simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4409 p hg
    simpa only [d5010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5942 (p : Pattern) (guard : d5011 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5010 p = 1 := by simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5941 p hg
    simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4410 p hg
    simpa only [d5011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5943 (p : Pattern) (guard : d5012 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5011 p = 1 := by simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5942 p hg
    simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4411 p hg
    simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5944 (p : Pattern) (guard : d5013 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5012 p = 1 := by simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5943 p hg
    simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5945 (p : Pattern) (guard : d5014 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5810 p hg
    simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5013 p = 1 := by simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5944 p hg
    simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5946 (p : Pattern) (guard : d5015 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5014 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5945 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4628 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5947 (p : Pattern) (guard : d5016 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5015 p = 1 := by simpa only [d5016, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5946 p hg
    simpa only [d5016, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5016, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d5016, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5948 (p : Pattern) (guard : d5017 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5016 p = 1 := by simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5947 p hg
    simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5834 p hg
    simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5949 (p : Pattern) (guard : d5018 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5017 p = 1 := by simpa only [d5018, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5948 p hg
    simpa only [d5018, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5018, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d5018, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5950 (p : Pattern) (guard : d5019 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5018 p = 1 := by simpa only [d5019, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5949 p hg
    simpa only [d5019, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5019, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d5019, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5951 (p : Pattern) (guard : d5020 p = 1) : d47664 p ≤ (-1 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5020, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4404 p hg
    simpa only [d5020, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5019 p = 1 := by simpa only [d5020, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5950 p hg
    simpa only [d5020, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5952 (p : Pattern) (guard : d5021 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5020 p = 1 := by simpa only [d5021, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5951 p hg
    simpa only [d5021, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5021, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4424 p hg
    simpa only [d5021, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5953 (p : Pattern) (guard : d5022 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5021 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5952 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5954 (p : Pattern) (guard : d5023 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5022 p = 1 := by simpa only [d5023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5953 p hg
    simpa only [d5023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4426 p hg
    simpa only [d5023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5955 (p : Pattern) (guard : d5024 p = 1) : d47685 p ≤ (-1 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d5009 p = 1 := by simpa only [d5024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5940 p hg
    simpa only [d5024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5023 p = 1 := by simpa only [d5024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5954 p hg
    simpa only [d5024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5956 (p : Pattern) (guard : d5025 p = 1) : d47686 p ≤ (-1 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5025, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4403 p hg
    simpa only [d5025, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5024 p = 1 := by simpa only [d5025, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5955 p hg
    simpa only [d5025, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5957 (p : Pattern) (guard : d5026 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5026, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4402 p hg
    simpa only [d5026, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5025 p = 1 := by simpa only [d5026, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5956 p hg
    simpa only [d5026, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5958 (p : Pattern) (guard : d5027 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d5026 p = 1 := by simpa only [d5027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5957 p hg
    simpa only [d5027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d5027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5959 (p : Pattern) (guard : d6955 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d6954 p = 1 := by simpa only [d6955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5939 p hg
    simpa only [d6955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5027 p = 1 := by simpa only [d6955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5958 p hg
    simpa only [d6955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5960 (p : Pattern) (guard : d6956 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d6955 p = 1 := by simpa only [d6956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5959 p hg
    simpa only [d6956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d6956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5961 (p : Pattern) (guard : d6957 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d6956 p = 1 := by simpa only [d6957, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5960 p hg
    simpa only [d6957, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6957, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d6957, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5962 (p : Pattern) (guard : d6958 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6958, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d6958, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6957 p = 1 := by simpa only [d6958, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5961 p hg
    simpa only [d6958, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5963 (p : Pattern) (guard : d6959 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1223 p = 1 := by simpa only [d6959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5938 p hg
    simpa only [d6959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6958 p = 1 := by simpa only [d6959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5962 p hg
    simpa only [d6959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5964 (p : Pattern) (guard : d6960 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6959 p = 1 := by simpa only [d6960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5963 p hg
    simpa only [d6960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5965 (p : Pattern) (guard : d6961 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6960 p = 1 := by simpa only [d6961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5964 p hg
    simpa only [d6961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5966 (p : Pattern) (guard : d6962 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6961 p = 1 := by simpa only [d6962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5965 p hg
    simpa only [d6962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5967 (p : Pattern) (guard : d5028 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d1145 p = 1 := by simpa only [d5028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5860 p hg
    simpa only [d5028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5027 p = 1 := by simpa only [d5028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5958 p hg
    simpa only [d5028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5968 (p : Pattern) (guard : d5029 p = 1) : d47687 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d5028 p = 1 := by simpa only [d5029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5967 p hg
    simpa only [d5029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4432 p hg
    simpa only [d5029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5969 (p : Pattern) (guard : d5030 p = 1) : d47699 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5029 p = 1 := by simpa only [d5030, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5968 p hg
    simpa only [d5030, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5030, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4436 p hg
    simpa only [d5030, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5970 (p : Pattern) (guard : d5031 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5031, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4401 p hg
    simpa only [d5031, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5030 p = 1 := by simpa only [d5031, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5969 p hg
    simpa only [d5031, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5971 (p : Pattern) (guard : d6963 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d5031 p = 1 := by simpa only [d6963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5970 p hg
    simpa only [d6963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1154 p = 1 := by simpa only [d6963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5869 p hg
    simpa only [d6963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5972 (p : Pattern) (guard : d6964 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6963 p = 1 := by simpa only [d6964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5971 p hg
    simpa only [d6964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5973 (p : Pattern) (guard : d6965 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6964 p = 1 := by simpa only [d6965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5972 p hg
    simpa only [d6965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5974 (p : Pattern) (guard : d6966 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6965 p = 1 := by simpa only [d6966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5973 p hg
    simpa only [d6966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5975 (p : Pattern) (guard : d6967 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6962 p = 1 := by simpa only [d6967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5966 p hg
    simpa only [d6967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6966 p = 1 := by simpa only [d6967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5974 p hg
    simpa only [d6967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5976 (p : Pattern) (guard : d82148 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6967 p = 1 := by simpa only [d82148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5975 p hg
    simpa only [d82148, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d82148, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82148, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5977 (p : Pattern) (guard : d6254 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1150 p = 1 := by simpa only [d6254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5865 p hg
    simpa only [d6254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5978 (p : Pattern) (guard : d6255 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d6254 p = 1 := by simpa only [d6255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5977 p hg
    simpa only [d6255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5979 (p : Pattern) (guard : d6256 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d6255 p = 1 := by simpa only [d6256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5978 p hg
    simpa only [d6256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5980 (p : Pattern) (guard : d6257 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d6257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6256 p = 1 := by simpa only [d6257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5979 p hg
    simpa only [d6257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5981 (p : Pattern) (guard : d6299 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d6257 p = 1 := by simpa only [d6299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5980 p hg
    simpa only [d6299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5982 (p : Pattern) (guard : d6300 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d6299 p = 1 := by simpa only [d6300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5981 p hg
    simpa only [d6300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5983 (p : Pattern) (guard : d82149 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d82148 p = 1 := by simpa only [d82149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5976 p hg
    simpa only [d82149, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d6300 p = 1 := by simpa only [d82149, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5982 p hg
    simpa only [d82149, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5984 (p : Pattern) (guard : d82150 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d1198 p = 1 := by simpa only [d82150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5913 p hg
    simpa only [d82150, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82149 p = 1 := by simpa only [d82150, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5983 p hg
    simpa only [d82150, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5985 (p : Pattern) (guard : d82151 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d1189 p = 1 := by simpa only [d82151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5904 p hg
    simpa only [d82151, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82150 p = 1 := by simpa only [d82151, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5984 p hg
    simpa only [d82151, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5986 (p : Pattern) (guard : d82152 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d82152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d82152, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d82151 p = 1 := by simpa only [d82152, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5985 p hg
    simpa only [d82152, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5987 (p : Pattern) (guard : d1326 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1182 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5897 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5988 (p : Pattern) (guard : d1327 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1184 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5899 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5989 (p : Pattern) (guard : d1328 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1326 p = 1 := by simpa only [d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5987 p hg
    simpa only [d1328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1327 p = 1 := by simpa only [d1328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5988 p hg
    simpa only [d1328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5990 (p : Pattern) (guard : d1329 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1328 p = 1 := by simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5989 p hg
    simpa only [d1329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5991 (p : Pattern) (guard : d1330 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1329 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5990 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5992 (p : Pattern) (guard : d1331 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1330 p = 1 := by simpa only [d1331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5991 p hg
    simpa only [d1331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5993 (p : Pattern) (guard : d1332 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1191 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5906 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5994 (p : Pattern) (guard : d1333 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1194 p = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5909 p hg
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5995 (p : Pattern) (guard : d1334 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1332 p = 1 := by simpa only [d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5993 p hg
    simpa only [d1334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1333 p = 1 := by simpa only [d1334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5994 p hg
    simpa only [d1334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5996 (p : Pattern) (guard : d1335 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1334 p = 1 := by simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5995 p hg
    simpa only [d1335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5997 (p : Pattern) (guard : d1336 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d1335 p = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5996 p hg
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d1336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5998 (p : Pattern) (guard : d6973 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6961 p = 1 := by simpa only [d6973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5965 p hg
    simpa only [d6973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare5999 (p : Pattern) (guard : d6974 p = 1) : d47700 p ≤ (-1 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d6965 p = 1 := by simpa only [d6974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5973 p hg
    simpa only [d6974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d6974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4400 p hg
    simpa only [d6974, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
