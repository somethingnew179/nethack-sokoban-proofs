import NetHack.Soko22Hazard87.Compare050
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare12750 (p : Pattern) (guard : d160999 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 251 with
  | false =>
    have hg : d160998 p = 1 := by simpa only [d160999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12749 p hg
    simpa only [d160999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d160999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12751 (p : Pattern) (guard : d161000 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 250 with
  | false =>
    have hg : d160999 p = 1 := by simpa only [d161000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12750 p hg
    simpa only [d161000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12752 (p : Pattern) (guard : d161001 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 249 with
  | false =>
    have hg : d161000 p = 1 := by simpa only [d161001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12751 p hg
    simpa only [d161001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12753 (p : Pattern) (guard : d161002 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 245 with
  | false =>
    have hg : d161001 p = 1 := by simpa only [d161002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12752 p hg
    simpa only [d161002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12754 (p : Pattern) (guard : d161003 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 200 with
  | false =>
    have hg : d161002 p = 1 := by simpa only [d161003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12753 p hg
    simpa only [d161003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12755 (p : Pattern) (guard : d161004 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 199 with
  | false =>
    have hg : d161003 p = 1 := by simpa only [d161004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12754 p hg
    simpa only [d161004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12756 (p : Pattern) (guard : d161005 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 186 with
  | false =>
    have hg : d161004 p = 1 := by simpa only [d161005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12755 p hg
    simpa only [d161005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12757 (p : Pattern) (guard : d161006 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 185 with
  | false =>
    have hg : d161005 p = 1 := by simpa only [d161006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12756 p hg
    simpa only [d161006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12758 (p : Pattern) (guard : d161007 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 184 with
  | false =>
    have hg : d161006 p = 1 := by simpa only [d161007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12757 p hg
    simpa only [d161007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12759 (p : Pattern) (guard : d161008 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 181 with
  | false =>
    have hg : d161007 p = 1 := by simpa only [d161008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12758 p hg
    simpa only [d161008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12760 (p : Pattern) (guard : d161009 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 177 with
  | false =>
    have hg : d161008 p = 1 := by simpa only [d161009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12759 p hg
    simpa only [d161009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12761 (p : Pattern) (guard : d161010 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 164 with
  | false =>
    have hg : d161009 p = 1 := by simpa only [d161010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12760 p hg
    simpa only [d161010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12762 (p : Pattern) (guard : d161011 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 156 with
  | false =>
    have hg : d161010 p = 1 := by simpa only [d161011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12761 p hg
    simpa only [d161011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12763 (p : Pattern) (guard : d161012 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 155 with
  | false =>
    have hg : d161011 p = 1 := by simpa only [d161012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12762 p hg
    simpa only [d161012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12764 (p : Pattern) (guard : d161013 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 134 with
  | false =>
    have hg : d161012 p = 1 := by simpa only [d161013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12763 p hg
    simpa only [d161013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12765 (p : Pattern) (guard : d161014 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 133 with
  | false =>
    have hg : d161013 p = 1 := by simpa only [d161014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12764 p hg
    simpa only [d161014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12766 (p : Pattern) (guard : d161015 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 120 with
  | false =>
    have hg : d161014 p = 1 := by simpa only [d161015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12765 p hg
    simpa only [d161015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12767 (p : Pattern) (guard : d161016 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 118 with
  | false =>
    have hg : d161015 p = 1 := by simpa only [d161016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12766 p hg
    simpa only [d161016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12768 (p : Pattern) (guard : d161017 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 114 with
  | false =>
    have hg : d161016 p = 1 := by simpa only [d161017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12767 p hg
    simpa only [d161017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12769 (p : Pattern) (guard : d161018 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 111 with
  | false =>
    have hg : d161017 p = 1 := by simpa only [d161018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12768 p hg
    simpa only [d161018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12770 (p : Pattern) (guard : d161019 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 98 with
  | false =>
    have hg : d161018 p = 1 := by simpa only [d161019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12769 p hg
    simpa only [d161019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12771 (p : Pattern) (guard : d161020 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 97 with
  | false =>
    have hg : d161019 p = 1 := by simpa only [d161020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12770 p hg
    simpa only [d161020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12772 (p : Pattern) (guard : d161021 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 94 with
  | false =>
    have hg : d161020 p = 1 := by simpa only [d161021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12771 p hg
    simpa only [d161021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12773 (p : Pattern) (guard : d161022 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 76 with
  | false =>
    have hg : d161021 p = 1 := by simpa only [d161022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12772 p hg
    simpa only [d161022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12774 (p : Pattern) (guard : d161023 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 67 with
  | false =>
    have hg : d161022 p = 1 := by simpa only [d161023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12773 p hg
    simpa only [d161023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12775 (p : Pattern) (guard : d161024 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 52 with
  | false =>
    have hg : d161023 p = 1 := by simpa only [d161024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12774 p hg
    simpa only [d161024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12776 (p : Pattern) (guard : d161025 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 47 with
  | false =>
    have hg : d161024 p = 1 := by simpa only [d161025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12775 p hg
    simpa only [d161025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12777 (p : Pattern) (guard : d161026 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 46 with
  | false =>
    have hg : d161025 p = 1 := by simpa only [d161026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12776 p hg
    simpa only [d161026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12778 (p : Pattern) (guard : d161027 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 45 with
  | false =>
    have hg : d161026 p = 1 := by simpa only [d161027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12777 p hg
    simpa only [d161027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12779 (p : Pattern) (guard : d161028 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 30 with
  | false =>
    have hg : d161027 p = 1 := by simpa only [d161028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12778 p hg
    simpa only [d161028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12780 (p : Pattern) (guard : d161029 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 29 with
  | false =>
    have hg : d161028 p = 1 := by simpa only [d161029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12779 p hg
    simpa only [d161029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12781 (p : Pattern) (guard : d161030 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 28 with
  | false =>
    have hg : d161029 p = 1 := by simpa only [d161030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12780 p hg
    simpa only [d161030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12782 (p : Pattern) (guard : d161031 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 27 with
  | false =>
    have hg : d161030 p = 1 := by simpa only [d161031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12781 p hg
    simpa only [d161031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12783 (p : Pattern) (guard : d161032 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  cases selected : p 25 with
  | false =>
    have hg : d161031 p = 1 := by simpa only [d161032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12782 p hg
    simpa only [d161032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10988 p hg
    simpa only [d161032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12784 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12785 (p : Pattern) (guard : d0 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12786 (p : Pattern) (guard : d0 p = 1) : d47697 p ≤ (-2 : Int) + d159767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12787 (p : Pattern) (guard : d0 p = 1) : d47676 p ≤ (-2 : Int) + d100908 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12788 (p : Pattern) (guard : d0 p = 1) : d47681 p ≤ (-2 : Int) + d47680 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12789 (p : Pattern) (guard : d0 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12790 (p : Pattern) (guard : d0 p = 1) : d47655 p ≤ (-2 : Int) + d47683 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12791 (p : Pattern) (guard : d27 p = 1) : d47664 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12790 p hg
    simpa only [d27, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7957 p hg
    simpa only [d27, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12792 (p : Pattern) (guard : d0 p = 1) : d47684 p ≤ (-2 : Int) + d47684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12793 (p : Pattern) (guard : d28 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12791 p hg
    simpa only [d28, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12792 p hg
    simpa only [d28, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12794 (p : Pattern) (guard : d159796 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d159796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d159796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12793 p hg
    simpa only [d159796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12795 (p : Pattern) (guard : d159797 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d159796 p = 1 := by simpa only [d159797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12794 p hg
    simpa only [d159797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d159797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12796 (p : Pattern) (guard : d159798 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d159797 p = 1 := by simpa only [d159798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12795 p hg
    simpa only [d159798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d159798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12797 (p : Pattern) (guard : d159799 p = 1) : d47686 p ≤ (-2 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159799, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12788 p hg
    simpa only [d159799, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159798 p = 1 := by simpa only [d159799, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12796 p hg
    simpa only [d159799, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12798 (p : Pattern) (guard : d159800 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159800, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12787 p hg
    simpa only [d159800, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159799 p = 1 := by simpa only [d159800, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12797 p hg
    simpa only [d159800, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12799 (p : Pattern) (guard : d0 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12800 (p : Pattern) (guard : d159801 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d159800 p = 1 := by simpa only [d159801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12798 p hg
    simpa only [d159801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d159801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12801 (p : Pattern) (guard : d159802 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d159801 p = 1 := by simpa only [d159802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12800 p hg
    simpa only [d159802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d159802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12802 (p : Pattern) (guard : d159803 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d159802 p = 1 := by simpa only [d159803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12801 p hg
    simpa only [d159803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d159803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12803 (p : Pattern) (guard : d0 p = 1) : d47698 p ≤ (-2 : Int) + d159768 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12804 (p : Pattern) (guard : d159804 p = 1) : d47699 p ≤ (-2 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d159803 p = 1 := by simpa only [d159804, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12802 p hg
    simpa only [d159804, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159804, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12803 p hg
    simpa only [d159804, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12805 (p : Pattern) (guard : d159805 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159805, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d159805, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159804 p = 1 := by simpa only [d159805, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12804 p hg
    simpa only [d159805, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12806 (p : Pattern) (guard : d159806 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d159805 p = 1 := by simpa only [d159806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12805 p hg
    simpa only [d159806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12807 (p : Pattern) (guard : d159807 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d159806 p = 1 := by simpa only [d159807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12806 p hg
    simpa only [d159807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12808 (p : Pattern) (guard : d159808 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d159807 p = 1 := by simpa only [d159808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12807 p hg
    simpa only [d159808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12809 (p : Pattern) (guard : d159809 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159808 p = 1 := by simpa only [d159809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12808 p hg
    simpa only [d159809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12810 (p : Pattern) (guard : d159810 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159809 p = 1 := by simpa only [d159810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12809 p hg
    simpa only [d159810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12811 (p : Pattern) (guard : d159864 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159810 p = 1 := by simpa only [d159864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12810 p hg
    simpa only [d159864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12812 (p : Pattern) (guard : d159865 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159864 p = 1 := by simpa only [d159865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12811 p hg
    simpa only [d159865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12813 (p : Pattern) (guard : d159866 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159865 p = 1 := by simpa only [d159866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12812 p hg
    simpa only [d159866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12814 (p : Pattern) (guard : d159867 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159866 p = 1 := by simpa only [d159867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12813 p hg
    simpa only [d159867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12815 (p : Pattern) (guard : d159868 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159867 p = 1 := by simpa only [d159868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12814 p hg
    simpa only [d159868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12816 (p : Pattern) (guard : d159816 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d159808 p = 1 := by simpa only [d159816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12808 p hg
    simpa only [d159816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12817 (p : Pattern) (guard : d159817 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159816 p = 1 := by simpa only [d159817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12816 p hg
    simpa only [d159817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12818 (p : Pattern) (guard : d159871 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159817 p = 1 := by simpa only [d159871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12817 p hg
    simpa only [d159871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12819 (p : Pattern) (guard : d159872 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159871 p = 1 := by simpa only [d159872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12818 p hg
    simpa only [d159872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12820 (p : Pattern) (guard : d159873 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159872 p = 1 := by simpa only [d159873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12819 p hg
    simpa only [d159873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12821 (p : Pattern) (guard : d159874 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159873 p = 1 := by simpa only [d159874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12820 p hg
    simpa only [d159874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12822 (p : Pattern) (guard : d159875 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d159867 p = 1 := by simpa only [d159875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12814 p hg
    simpa only [d159875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159874 p = 1 := by simpa only [d159875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12821 p hg
    simpa only [d159875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12823 (p : Pattern) (guard : d159876 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d159868 p = 1 := by simpa only [d159876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12815 p hg
    simpa only [d159876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159875 p = 1 := by simpa only [d159876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12822 p hg
    simpa only [d159876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12824 (p : Pattern) (guard : d159877 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d159876 p = 1 := by simpa only [d159877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12823 p hg
    simpa only [d159877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12825 (p : Pattern) (guard : d161033 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d159877 p = 1 := by simpa only [d161033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12824 p hg
    simpa only [d161033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12826 (p : Pattern) (guard : d161034 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161033 p = 1 := by simpa only [d161034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12825 p hg
    simpa only [d161034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12827 (p : Pattern) (guard : d0 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12828 (p : Pattern) (guard : d0 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12829 (p : Pattern) (guard : d0 p = 1) : d47763 p ≤ (-2 : Int) + d159774 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12830 (p : Pattern) (guard : d0 p = 1) : d47746 p ≤ (-2 : Int) + d100911 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12831 (p : Pattern) (guard : d0 p = 1) : d47751 p ≤ (-2 : Int) + d47750 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12832 (p : Pattern) (guard : d0 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12833 (p : Pattern) (guard : d0 p = 1) : d47734 p ≤ (-2 : Int) + d47753 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12834 (p : Pattern) (guard : d27 p = 1) : d47737 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12833 p hg
    simpa only [d27, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8019 p hg
    simpa only [d27, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12835 (p : Pattern) (guard : d0 p = 1) : d47754 p ≤ (-2 : Int) + d47754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12836 (p : Pattern) (guard : d28 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12834 p hg
    simpa only [d28, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12835 p hg
    simpa only [d28, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12837 (p : Pattern) (guard : d159796 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d159796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d159796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12836 p hg
    simpa only [d159796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12838 (p : Pattern) (guard : d159797 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d159796 p = 1 := by simpa only [d159797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12837 p hg
    simpa only [d159797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d159797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12839 (p : Pattern) (guard : d159798 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d159797 p = 1 := by simpa only [d159798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12838 p hg
    simpa only [d159798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d159798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12840 (p : Pattern) (guard : d159799 p = 1) : d47756 p ≤ (-2 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159799, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12831 p hg
    simpa only [d159799, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159798 p = 1 := by simpa only [d159799, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12839 p hg
    simpa only [d159799, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12841 (p : Pattern) (guard : d159800 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159800, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12830 p hg
    simpa only [d159800, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159799 p = 1 := by simpa only [d159800, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12840 p hg
    simpa only [d159800, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12842 (p : Pattern) (guard : d0 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12843 (p : Pattern) (guard : d159801 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d159800 p = 1 := by simpa only [d159801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12841 p hg
    simpa only [d159801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d159801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12844 (p : Pattern) (guard : d159802 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d159801 p = 1 := by simpa only [d159802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12843 p hg
    simpa only [d159802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d159802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12845 (p : Pattern) (guard : d159803 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d159802 p = 1 := by simpa only [d159803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12844 p hg
    simpa only [d159803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d159803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12846 (p : Pattern) (guard : d0 p = 1) : d47764 p ≤ (-2 : Int) + d159773 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12847 (p : Pattern) (guard : d159804 p = 1) : d47765 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d159803 p = 1 := by simpa only [d159804, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12845 p hg
    simpa only [d159804, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159804, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12846 p hg
    simpa only [d159804, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12848 (p : Pattern) (guard : d159805 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159805, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12829 p hg
    simpa only [d159805, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159804 p = 1 := by simpa only [d159805, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12847 p hg
    simpa only [d159805, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12849 (p : Pattern) (guard : d159806 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d159805 p = 1 := by simpa only [d159806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12848 p hg
    simpa only [d159806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d159806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12850 (p : Pattern) (guard : d159807 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d159806 p = 1 := by simpa only [d159807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12849 p hg
    simpa only [d159807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d159807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12851 (p : Pattern) (guard : d159808 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d159807 p = 1 := by simpa only [d159808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12850 p hg
    simpa only [d159808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d159808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12852 (p : Pattern) (guard : d159816 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d159808 p = 1 := by simpa only [d159816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12851 p hg
    simpa only [d159816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d159816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12853 (p : Pattern) (guard : d159817 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159816 p = 1 := by simpa only [d159817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12852 p hg
    simpa only [d159817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d159817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12854 (p : Pattern) (guard : d159871 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d159871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159817 p = 1 := by simpa only [d159871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12853 p hg
    simpa only [d159871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12855 (p : Pattern) (guard : d159872 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159871 p = 1 := by simpa only [d159872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12854 p hg
    simpa only [d159872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d159872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12856 (p : Pattern) (guard : d159873 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d159873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159872 p = 1 := by simpa only [d159873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12855 p hg
    simpa only [d159873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12857 (p : Pattern) (guard : d159874 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d159874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159873 p = 1 := by simpa only [d159874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12856 p hg
    simpa only [d159874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12858 (p : Pattern) (guard : d160055 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160055, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160055, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159874 p = 1 := by simpa only [d160055, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12857 p hg
    simpa only [d160055, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12859 (p : Pattern) (guard : d160056 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d160056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160055 p = 1 := by simpa only [d160056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12858 p hg
    simpa only [d160056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12860 (p : Pattern) (guard : d161035 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160056 p = 1 := by simpa only [d161035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12859 p hg
    simpa only [d161035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12861 (p : Pattern) (guard : d161036 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 51 with
  | false =>
    have hg : d161035 p = 1 := by simpa only [d161036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12860 p hg
    simpa only [d161036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12862 (p : Pattern) (guard : d161037 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 50 with
  | false =>
    have hg : d161036 p = 1 := by simpa only [d161037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12861 p hg
    simpa only [d161037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12863 (p : Pattern) (guard : d161038 p = 1) : d47768 p ≤ (-2 : Int) + d159776 p := by
  cases selected : p 49 with
  | false =>
    have hg : d161034 p = 1 := by simpa only [d161038, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12826 p hg
    simpa only [d161038, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161037 p = 1 := by simpa only [d161038, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12862 p hg
    simpa only [d161038, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12864 (p : Pattern) (guard : d0 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12865 (p : Pattern) (guard : d0 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12866 (p : Pattern) (guard : d0 p = 1) : d47786 p ≤ (-2 : Int) + d159777 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12867 (p : Pattern) (guard : d0 p = 1) : d47796 p ≤ (-2 : Int) + d47795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12868 (p : Pattern) (guard : d0 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12869 (p : Pattern) (guard : d0 p = 1) : d47652 p ≤ (-2 : Int) + d47792 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12870 (p : Pattern) (guard : d66 p = 1) : d47652 p ≤ (-2 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d66, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12869 p hg
    simpa only [d66, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d24 p = 1 := by simpa only [d66, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8070 p hg
    simpa only [d66, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12871 (p : Pattern) (guard : d67 p = 1) : d47798 p ≤ (-2 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d66 p = 1 := by simpa only [d67, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12870 p hg
    simpa only [d67, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d25 p = 1 := by simpa only [d67, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8072 p hg
    simpa only [d67, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12872 (p : Pattern) (guard : d68 p = 1) : d47799 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d67 p = 1 := by simpa only [d68, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12871 p hg
    simpa only [d68, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d68, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8090 p hg
    simpa only [d68, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12873 (p : Pattern) (guard : d0 p = 1) : d47802 p ≤ (-2 : Int) + d47802 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12874 (p : Pattern) (guard : d69 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d68 p = 1 := by simpa only [d69, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12872 p hg
    simpa only [d69, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d69, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12873 p hg
    simpa only [d69, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12875 (p : Pattern) (guard : d159833 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d159833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d69 p = 1 := by simpa only [d159833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12874 p hg
    simpa only [d159833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12876 (p : Pattern) (guard : d159834 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d159833 p = 1 := by simpa only [d159834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12875 p hg
    simpa only [d159834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d159834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12877 (p : Pattern) (guard : d159835 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d159834 p = 1 := by simpa only [d159835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12876 p hg
    simpa only [d159835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d159835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12878 (p : Pattern) (guard : d159836 p = 1) : d47804 p ≤ (-2 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159836, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12867 p hg
    simpa only [d159836, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159835 p = 1 := by simpa only [d159836, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12877 p hg
    simpa only [d159836, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12879 (p : Pattern) (guard : d159837 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159837, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12866 p hg
    simpa only [d159837, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159836 p = 1 := by simpa only [d159837, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12878 p hg
    simpa only [d159837, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12880 (p : Pattern) (guard : d0 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12881 (p : Pattern) (guard : d159838 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d159837 p = 1 := by simpa only [d159838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12879 p hg
    simpa only [d159838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d159838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12882 (p : Pattern) (guard : d159839 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d159838 p = 1 := by simpa only [d159839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12881 p hg
    simpa only [d159839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d159839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12883 (p : Pattern) (guard : d159840 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d159839 p = 1 := by simpa only [d159840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12882 p hg
    simpa only [d159840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d159840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12884 (p : Pattern) (guard : d0 p = 1) : d47806 p ≤ (-2 : Int) + d159780 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12885 (p : Pattern) (guard : d159841 p = 1) : d47807 p ≤ (-2 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d159840 p = 1 := by simpa only [d159841, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12883 p hg
    simpa only [d159841, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159841, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12884 p hg
    simpa only [d159841, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12886 (p : Pattern) (guard : d159842 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159842, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d159842, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159841 p = 1 := by simpa only [d159842, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12885 p hg
    simpa only [d159842, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12887 (p : Pattern) (guard : d159843 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d159842 p = 1 := by simpa only [d159843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12886 p hg
    simpa only [d159843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d159843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12888 (p : Pattern) (guard : d159844 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d159843 p = 1 := by simpa only [d159844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12887 p hg
    simpa only [d159844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d159844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12889 (p : Pattern) (guard : d159845 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d159844 p = 1 := by simpa only [d159845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12888 p hg
    simpa only [d159845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d159845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12890 (p : Pattern) (guard : d159846 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d159845 p = 1 := by simpa only [d159846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12889 p hg
    simpa only [d159846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d159846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12891 (p : Pattern) (guard : d159847 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159846 p = 1 := by simpa only [d159847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12890 p hg
    simpa only [d159847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d159847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12892 (p : Pattern) (guard : d160088 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159847 p = 1 := by simpa only [d160088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12891 p hg
    simpa only [d160088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12893 (p : Pattern) (guard : d160089 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160088 p = 1 := by simpa only [d160089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12892 p hg
    simpa only [d160089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12894 (p : Pattern) (guard : d160090 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160089 p = 1 := by simpa only [d160090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12893 p hg
    simpa only [d160090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12895 (p : Pattern) (guard : d160091 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160090 p = 1 := by simpa only [d160091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12894 p hg
    simpa only [d160091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12896 (p : Pattern) (guard : d160092 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160092, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160092, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160091 p = 1 := by simpa only [d160092, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12895 p hg
    simpa only [d160092, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12897 (p : Pattern) (guard : d160093 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d160093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160092 p = 1 := by simpa only [d160093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12896 p hg
    simpa only [d160093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12898 (p : Pattern) (guard : d161039 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160093 p = 1 := by simpa only [d161039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12897 p hg
    simpa only [d161039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12899 (p : Pattern) (guard : d161040 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 51 with
  | false =>
    have hg : d161039 p = 1 := by simpa only [d161040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12898 p hg
    simpa only [d161040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12900 (p : Pattern) (guard : d161041 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 50 with
  | false =>
    have hg : d161040 p = 1 := by simpa only [d161041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12899 p hg
    simpa only [d161041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12901 (p : Pattern) (guard : d0 p = 1) : d47864 p ≤ (-2 : Int) + d159793 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare12902 (p : Pattern) (guard : d161042 p = 1) : d47865 p ≤ (-2 : Int) + d159794 p := by
  cases selected : p 49 with
  | false =>
    have hg : d161041 p = 1 := by simpa only [d161042, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12900 p hg
    simpa only [d161042, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161042, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12901 p hg
    simpa only [d161042, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12903 (p : Pattern) (guard : d161043 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 48 with
  | false =>
    have hg : d161038 p = 1 := by simpa only [d161043, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12863 p hg
    simpa only [d161043, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161042 p = 1 := by simpa only [d161043, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12902 p hg
    simpa only [d161043, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12904 (p : Pattern) (guard : d161044 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161043 p = 1 := by simpa only [d161044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12903 p hg
    simpa only [d161044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12905 (p : Pattern) (guard : d161045 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161044 p = 1 := by simpa only [d161045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12904 p hg
    simpa only [d161045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12906 (p : Pattern) (guard : d161046 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161045 p = 1 := by simpa only [d161046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12905 p hg
    simpa only [d161046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12907 (p : Pattern) (guard : d161047 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161046 p = 1 := by simpa only [d161047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12906 p hg
    simpa only [d161047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12908 (p : Pattern) (guard : d161048 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161047 p = 1 := by simpa only [d161048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12907 p hg
    simpa only [d161048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12909 (p : Pattern) (guard : d161049 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161048 p = 1 := by simpa only [d161049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12908 p hg
    simpa only [d161049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12910 (p : Pattern) (guard : d141 p = 1) : d47664 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d141, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12790 p hg
    simpa only [d141, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d141, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8143 p hg
    simpa only [d141, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12911 (p : Pattern) (guard : d142 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12910 p hg
    simpa only [d142, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12792 p hg
    simpa only [d142, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12912 (p : Pattern) (guard : d159891 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d159891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d159891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12911 p hg
    simpa only [d159891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12913 (p : Pattern) (guard : d159892 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d159891 p = 1 := by simpa only [d159892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12912 p hg
    simpa only [d159892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12789 p hg
    simpa only [d159892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12914 (p : Pattern) (guard : d159893 p = 1) : d47685 p ≤ (-2 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d159892 p = 1 := by simpa only [d159893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12913 p hg
    simpa only [d159893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159797 p = 1 := by simpa only [d159893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12795 p hg
    simpa only [d159893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12915 (p : Pattern) (guard : d159894 p = 1) : d47686 p ≤ (-2 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159894, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12788 p hg
    simpa only [d159894, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159893 p = 1 := by simpa only [d159894, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12914 p hg
    simpa only [d159894, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12916 (p : Pattern) (guard : d159895 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159895, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12787 p hg
    simpa only [d159895, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159894 p = 1 := by simpa only [d159895, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12915 p hg
    simpa only [d159895, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12917 (p : Pattern) (guard : d159896 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d159895 p = 1 := by simpa only [d159896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12916 p hg
    simpa only [d159896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159800 p = 1 := by simpa only [d159896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12798 p hg
    simpa only [d159896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12918 (p : Pattern) (guard : d159897 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d159896 p = 1 := by simpa only [d159897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12917 p hg
    simpa only [d159897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159801 p = 1 := by simpa only [d159897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12800 p hg
    simpa only [d159897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12919 (p : Pattern) (guard : d159898 p = 1) : d47687 p ≤ (-2 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d159897 p = 1 := by simpa only [d159898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12918 p hg
    simpa only [d159898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12799 p hg
    simpa only [d159898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12920 (p : Pattern) (guard : d159899 p = 1) : d47699 p ≤ (-2 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d159898 p = 1 := by simpa only [d159899, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12919 p hg
    simpa only [d159899, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159899, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12803 p hg
    simpa only [d159899, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12921 (p : Pattern) (guard : d159900 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159900, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d159900, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159899 p = 1 := by simpa only [d159900, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12920 p hg
    simpa only [d159900, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12922 (p : Pattern) (guard : d159901 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d159900 p = 1 := by simpa only [d159901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12921 p hg
    simpa only [d159901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159805 p = 1 := by simpa only [d159901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12805 p hg
    simpa only [d159901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12923 (p : Pattern) (guard : d159902 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d159901 p = 1 := by simpa only [d159902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12922 p hg
    simpa only [d159902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12924 (p : Pattern) (guard : d159903 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d159902 p = 1 := by simpa only [d159903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12923 p hg
    simpa only [d159903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12925 (p : Pattern) (guard : d159904 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159903 p = 1 := by simpa only [d159904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12924 p hg
    simpa only [d159904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12926 (p : Pattern) (guard : d159905 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159904 p = 1 := by simpa only [d159905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12925 p hg
    simpa only [d159905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159809 p = 1 := by simpa only [d159905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12809 p hg
    simpa only [d159905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12927 (p : Pattern) (guard : d159973 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159905 p = 1 := by simpa only [d159973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12926 p hg
    simpa only [d159973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12928 (p : Pattern) (guard : d159974 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159973 p = 1 := by simpa only [d159974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12927 p hg
    simpa only [d159974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12929 (p : Pattern) (guard : d159975 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159974 p = 1 := by simpa only [d159975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12928 p hg
    simpa only [d159975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12930 (p : Pattern) (guard : d159976 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159975 p = 1 := by simpa only [d159976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12929 p hg
    simpa only [d159976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12931 (p : Pattern) (guard : d159977 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159977, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159976 p = 1 := by simpa only [d159977, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12930 p hg
    simpa only [d159977, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12932 (p : Pattern) (guard : d159920 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d159903 p = 1 := by simpa only [d159920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12924 p hg
    simpa only [d159920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12933 (p : Pattern) (guard : d159921 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159920 p = 1 := by simpa only [d159921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12932 p hg
    simpa only [d159921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159816 p = 1 := by simpa only [d159921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12816 p hg
    simpa only [d159921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12934 (p : Pattern) (guard : d159980 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159921 p = 1 := by simpa only [d159980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12933 p hg
    simpa only [d159980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12935 (p : Pattern) (guard : d159981 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159980 p = 1 := by simpa only [d159981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12934 p hg
    simpa only [d159981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12936 (p : Pattern) (guard : d159982 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159981 p = 1 := by simpa only [d159982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12935 p hg
    simpa only [d159982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12937 (p : Pattern) (guard : d159983 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159982 p = 1 := by simpa only [d159983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12936 p hg
    simpa only [d159983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12938 (p : Pattern) (guard : d159984 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d159976 p = 1 := by simpa only [d159984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12930 p hg
    simpa only [d159984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159983 p = 1 := by simpa only [d159984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12937 p hg
    simpa only [d159984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12939 (p : Pattern) (guard : d159985 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d159977 p = 1 := by simpa only [d159985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12931 p hg
    simpa only [d159985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159984 p = 1 := by simpa only [d159985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12938 p hg
    simpa only [d159985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12940 (p : Pattern) (guard : d159986 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d159985 p = 1 := by simpa only [d159986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12939 p hg
    simpa only [d159986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d159986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12941 (p : Pattern) (guard : d161050 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d159986 p = 1 := by simpa only [d161050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12940 p hg
    simpa only [d161050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12942 (p : Pattern) (guard : d161051 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161050 p = 1 := by simpa only [d161051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12941 p hg
    simpa only [d161051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12943 (p : Pattern) (guard : d141 p = 1) : d47737 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d141, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12833 p hg
    simpa only [d141, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d141, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8191 p hg
    simpa only [d141, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12944 (p : Pattern) (guard : d142 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d141 p = 1 := by simpa only [d142, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12943 p hg
    simpa only [d142, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d142, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12835 p hg
    simpa only [d142, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12945 (p : Pattern) (guard : d159891 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d159891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d142 p = 1 := by simpa only [d159891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12944 p hg
    simpa only [d159891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12946 (p : Pattern) (guard : d159892 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d159891 p = 1 := by simpa only [d159892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12945 p hg
    simpa only [d159892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d159892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12947 (p : Pattern) (guard : d159893 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d159892 p = 1 := by simpa only [d159893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12946 p hg
    simpa only [d159893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159797 p = 1 := by simpa only [d159893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12838 p hg
    simpa only [d159893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12948 (p : Pattern) (guard : d159894 p = 1) : d47756 p ≤ (-2 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159894, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12831 p hg
    simpa only [d159894, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159893 p = 1 := by simpa only [d159894, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12947 p hg
    simpa only [d159894, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12949 (p : Pattern) (guard : d159895 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159895, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12830 p hg
    simpa only [d159895, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159894 p = 1 := by simpa only [d159895, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12948 p hg
    simpa only [d159895, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12950 (p : Pattern) (guard : d159896 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d159895 p = 1 := by simpa only [d159896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12949 p hg
    simpa only [d159896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159800 p = 1 := by simpa only [d159896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12841 p hg
    simpa only [d159896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12951 (p : Pattern) (guard : d159897 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d159896 p = 1 := by simpa only [d159897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12950 p hg
    simpa only [d159897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159801 p = 1 := by simpa only [d159897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12843 p hg
    simpa only [d159897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12952 (p : Pattern) (guard : d159898 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d159897 p = 1 := by simpa only [d159898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12951 p hg
    simpa only [d159898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d159898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12953 (p : Pattern) (guard : d159899 p = 1) : d47765 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d159898 p = 1 := by simpa only [d159899, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12952 p hg
    simpa only [d159899, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159899, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12846 p hg
    simpa only [d159899, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12954 (p : Pattern) (guard : d159900 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159900, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12829 p hg
    simpa only [d159900, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159899 p = 1 := by simpa only [d159900, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12953 p hg
    simpa only [d159900, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12955 (p : Pattern) (guard : d159901 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d159900 p = 1 := by simpa only [d159901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12954 p hg
    simpa only [d159901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159805 p = 1 := by simpa only [d159901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12848 p hg
    simpa only [d159901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12956 (p : Pattern) (guard : d159902 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d159901 p = 1 := by simpa only [d159902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12955 p hg
    simpa only [d159902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d159902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12957 (p : Pattern) (guard : d159903 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d159902 p = 1 := by simpa only [d159903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12956 p hg
    simpa only [d159903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d159903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12958 (p : Pattern) (guard : d159920 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d159903 p = 1 := by simpa only [d159920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12957 p hg
    simpa only [d159920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d159920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12959 (p : Pattern) (guard : d159921 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159920 p = 1 := by simpa only [d159921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12958 p hg
    simpa only [d159921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159816 p = 1 := by simpa only [d159921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12852 p hg
    simpa only [d159921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12960 (p : Pattern) (guard : d159980 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d159980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159921 p = 1 := by simpa only [d159980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12959 p hg
    simpa only [d159980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12961 (p : Pattern) (guard : d159981 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d159980 p = 1 := by simpa only [d159981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12960 p hg
    simpa only [d159981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d159981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12962 (p : Pattern) (guard : d159982 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d159982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159981 p = 1 := by simpa only [d159982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12961 p hg
    simpa only [d159982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12963 (p : Pattern) (guard : d159983 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d159983, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159982 p = 1 := by simpa only [d159983, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12962 p hg
    simpa only [d159983, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12964 (p : Pattern) (guard : d161052 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161052, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161052, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159983 p = 1 := by simpa only [d161052, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12963 p hg
    simpa only [d161052, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12965 (p : Pattern) (guard : d161053 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161052 p = 1 := by simpa only [d161053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12964 p hg
    simpa only [d161053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12966 (p : Pattern) (guard : d161054 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 69 with
  | false =>
    have hg : d161053 p = 1 := by simpa only [d161054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12965 p hg
    simpa only [d161054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12967 (p : Pattern) (guard : d161055 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 51 with
  | false =>
    have hg : d161054 p = 1 := by simpa only [d161055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12966 p hg
    simpa only [d161055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12968 (p : Pattern) (guard : d161056 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 50 with
  | false =>
    have hg : d161055 p = 1 := by simpa only [d161056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12967 p hg
    simpa only [d161056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12969 (p : Pattern) (guard : d161057 p = 1) : d47768 p ≤ (-2 : Int) + d159776 p := by
  cases selected : p 49 with
  | false =>
    have hg : d161051 p = 1 := by simpa only [d161057, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12942 p hg
    simpa only [d161057, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161056 p = 1 := by simpa only [d161057, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12968 p hg
    simpa only [d161057, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12970 (p : Pattern) (guard : d226 p = 1) : d47652 p ≤ (-2 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d226, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12869 p hg
    simpa only [d226, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d138 p = 1 := by simpa only [d226, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8231 p hg
    simpa only [d226, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12971 (p : Pattern) (guard : d227 p = 1) : d47798 p ≤ (-2 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d226 p = 1 := by simpa only [d227, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12970 p hg
    simpa only [d227, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d139 p = 1 := by simpa only [d227, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8233 p hg
    simpa only [d227, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12972 (p : Pattern) (guard : d228 p = 1) : d47799 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d227 p = 1 := by simpa only [d228, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12971 p hg
    simpa only [d228, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d140 p = 1 := by simpa only [d228, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8249 p hg
    simpa only [d228, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12973 (p : Pattern) (guard : d229 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d228 p = 1 := by simpa only [d229, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12972 p hg
    simpa only [d229, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d229, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12873 p hg
    simpa only [d229, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12974 (p : Pattern) (guard : d159941 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d159941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d229 p = 1 := by simpa only [d159941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12973 p hg
    simpa only [d159941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12975 (p : Pattern) (guard : d159942 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d159941 p = 1 := by simpa only [d159942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12974 p hg
    simpa only [d159942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d159942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12976 (p : Pattern) (guard : d159943 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d159942 p = 1 := by simpa only [d159943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12975 p hg
    simpa only [d159943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159834 p = 1 := by simpa only [d159943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12876 p hg
    simpa only [d159943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12977 (p : Pattern) (guard : d159944 p = 1) : d47804 p ≤ (-2 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159944, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12867 p hg
    simpa only [d159944, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159943 p = 1 := by simpa only [d159944, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12976 p hg
    simpa only [d159944, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12978 (p : Pattern) (guard : d159945 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159945, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12866 p hg
    simpa only [d159945, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159944 p = 1 := by simpa only [d159945, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12977 p hg
    simpa only [d159945, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12979 (p : Pattern) (guard : d159946 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d159945 p = 1 := by simpa only [d159946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12978 p hg
    simpa only [d159946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159837 p = 1 := by simpa only [d159946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12879 p hg
    simpa only [d159946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12980 (p : Pattern) (guard : d159947 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d159946 p = 1 := by simpa only [d159947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12979 p hg
    simpa only [d159947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159838 p = 1 := by simpa only [d159947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12881 p hg
    simpa only [d159947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12981 (p : Pattern) (guard : d159948 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d159947 p = 1 := by simpa only [d159948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12980 p hg
    simpa only [d159948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d159948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12982 (p : Pattern) (guard : d159949 p = 1) : d47807 p ≤ (-2 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d159948 p = 1 := by simpa only [d159949, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12981 p hg
    simpa only [d159949, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159949, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12884 p hg
    simpa only [d159949, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12983 (p : Pattern) (guard : d159950 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159950, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d159950, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159949 p = 1 := by simpa only [d159950, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12982 p hg
    simpa only [d159950, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12984 (p : Pattern) (guard : d159951 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d159950 p = 1 := by simpa only [d159951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12983 p hg
    simpa only [d159951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159842 p = 1 := by simpa only [d159951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12886 p hg
    simpa only [d159951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12985 (p : Pattern) (guard : d159952 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d159951 p = 1 := by simpa only [d159952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12984 p hg
    simpa only [d159952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d159952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12986 (p : Pattern) (guard : d159953 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d159952 p = 1 := by simpa only [d159953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12985 p hg
    simpa only [d159953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d159953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12987 (p : Pattern) (guard : d159954 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d159953 p = 1 := by simpa only [d159954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12986 p hg
    simpa only [d159954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d159954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12988 (p : Pattern) (guard : d159955 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d159954 p = 1 := by simpa only [d159955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12987 p hg
    simpa only [d159955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159846 p = 1 := by simpa only [d159955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12890 p hg
    simpa only [d159955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12989 (p : Pattern) (guard : d161058 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d159955 p = 1 := by simpa only [d161058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12988 p hg
    simpa only [d161058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12990 (p : Pattern) (guard : d161059 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d161058 p = 1 := by simpa only [d161059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12989 p hg
    simpa only [d161059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12991 (p : Pattern) (guard : d161060 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161059 p = 1 := by simpa only [d161060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12990 p hg
    simpa only [d161060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12992 (p : Pattern) (guard : d161061 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161060 p = 1 := by simpa only [d161061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12991 p hg
    simpa only [d161061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12993 (p : Pattern) (guard : d161062 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161062, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161062, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161061 p = 1 := by simpa only [d161062, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12992 p hg
    simpa only [d161062, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12994 (p : Pattern) (guard : d161063 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161062 p = 1 := by simpa only [d161063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12993 p hg
    simpa only [d161063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12995 (p : Pattern) (guard : d161064 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 69 with
  | false =>
    have hg : d161063 p = 1 := by simpa only [d161064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12994 p hg
    simpa only [d161064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12996 (p : Pattern) (guard : d161065 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 51 with
  | false =>
    have hg : d161064 p = 1 := by simpa only [d161065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12995 p hg
    simpa only [d161065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12997 (p : Pattern) (guard : d161066 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 50 with
  | false =>
    have hg : d161065 p = 1 := by simpa only [d161066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12996 p hg
    simpa only [d161066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12998 (p : Pattern) (guard : d161067 p = 1) : d47865 p ≤ (-2 : Int) + d159794 p := by
  cases selected : p 49 with
  | false =>
    have hg : d161066 p = 1 := by simpa only [d161067, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12997 p hg
    simpa only [d161067, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161067, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12901 p hg
    simpa only [d161067, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare12999 (p : Pattern) (guard : d161068 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 48 with
  | false =>
    have hg : d161057 p = 1 := by simpa only [d161068, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12969 p hg
    simpa only [d161068, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161067 p = 1 := by simpa only [d161068, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12998 p hg
    simpa only [d161068, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
