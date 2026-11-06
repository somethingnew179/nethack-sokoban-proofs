import NetHack.Soko22Hazard87.Compare046
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare11750 (p : Pattern) (guard : d160367 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160366 p = 1 := by simpa only [d160367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11749 p hg
    simpa only [d160367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11751 (p : Pattern) (guard : d160368 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160367 p = 1 := by simpa only [d160368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11750 p hg
    simpa only [d160368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11752 (p : Pattern) (guard : d160369 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160368 p = 1 := by simpa only [d160369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11751 p hg
    simpa only [d160369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11753 (p : Pattern) (guard : d160370 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160335 p = 1 := by simpa only [d160370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11718 p hg
    simpa only [d160370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11754 (p : Pattern) (guard : d160371 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160370 p = 1 := by simpa only [d160371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11753 p hg
    simpa only [d160371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11755 (p : Pattern) (guard : d160372 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160371 p = 1 := by simpa only [d160372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11754 p hg
    simpa only [d160372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11756 (p : Pattern) (guard : d160373 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160339 p = 1 := by simpa only [d160373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11722 p hg
    simpa only [d160373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11757 (p : Pattern) (guard : d160374 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160373 p = 1 := by simpa only [d160374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11756 p hg
    simpa only [d160374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11758 (p : Pattern) (guard : d160375 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160374 p = 1 := by simpa only [d160375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11757 p hg
    simpa only [d160375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11759 (p : Pattern) (guard : d160376 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160372 p = 1 := by simpa only [d160376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11755 p hg
    simpa only [d160376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160375 p = 1 := by simpa only [d160376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11758 p hg
    simpa only [d160376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11760 (p : Pattern) (guard : d160377 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160376 p = 1 := by simpa only [d160377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11759 p hg
    simpa only [d160377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11761 (p : Pattern) (guard : d160378 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160377 p = 1 := by simpa only [d160378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11760 p hg
    simpa only [d160378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11762 (p : Pattern) (guard : d1102 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1102, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d1102, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1102, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5816 p hg
    simpa only [d1102, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11763 (p : Pattern) (guard : d1103 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11762 p hg
    simpa only [d1103, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d1103, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11764 (p : Pattern) (guard : d160379 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1103 p = 1 := by simpa only [d160379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11763 p hg
    simpa only [d160379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11765 (p : Pattern) (guard : d160380 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160379 p = 1 := by simpa only [d160380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11764 p hg
    simpa only [d160380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11766 (p : Pattern) (guard : d160381 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160380 p = 1 := by simpa only [d160381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11765 p hg
    simpa only [d160381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160316 p = 1 := by simpa only [d160381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11697 p hg
    simpa only [d160381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11767 (p : Pattern) (guard : d160382 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160382, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d160382, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160381 p = 1 := by simpa only [d160382, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11766 p hg
    simpa only [d160382, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11768 (p : Pattern) (guard : d160383 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160383, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d160383, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160382 p = 1 := by simpa only [d160383, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11767 p hg
    simpa only [d160383, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11769 (p : Pattern) (guard : d9452 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5011 p = 1 := by simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5942 p hg
    simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11770 (p : Pattern) (guard : d9453 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d9452 p = 1 := by simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11769 p hg
    simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11771 (p : Pattern) (guard : d9795 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5810 p hg
    simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11770 p hg
    simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11772 (p : Pattern) (guard : d9796 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4627 p hg
    simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4408 p hg
    simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11773 (p : Pattern) (guard : d9797 p = 1) : d47617 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9795 p = 1 := by simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11771 p hg
    simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9796 p = 1 := by simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11772 p hg
    simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11774 (p : Pattern) (guard : d9798 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9797 p = 1 := by simpa only [d9798, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11773 p hg
    simpa only [d9798, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9798, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4416 p hg
    simpa only [d9798, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11775 (p : Pattern) (guard : d13024 p = 1) : d47619 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9798 p = 1 := by simpa only [d13024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11774 p hg
    simpa only [d13024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4418 p hg
    simpa only [d13024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11776 (p : Pattern) (guard : d13025 p = 1) : d47660 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d13024 p = 1 := by simpa only [d13025, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11775 p hg
    simpa only [d13025, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13025, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4420 p hg
    simpa only [d13025, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11777 (p : Pattern) (guard : d13026 p = 1) : d47663 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d13025 p = 1 := by simpa only [d13026, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11776 p hg
    simpa only [d13026, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13026, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3399 p hg
    simpa only [d13026, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11778 (p : Pattern) (guard : d13027 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13027, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d13027, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13026 p = 1 := by simpa only [d13027, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11777 p hg
    simpa only [d13027, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11779 (p : Pattern) (guard : d13028 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13027 p = 1 := by simpa only [d13028, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11778 p hg
    simpa only [d13028, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13028, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d13028, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11780 (p : Pattern) (guard : d160384 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13028 p = 1 := by simpa only [d160384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11779 p hg
    simpa only [d160384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11781 (p : Pattern) (guard : d160385 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160384 p = 1 := by simpa only [d160385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11780 p hg
    simpa only [d160385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d160385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11782 (p : Pattern) (guard : d160386 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160316 p = 1 := by simpa only [d160386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11697 p hg
    simpa only [d160386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160385 p = 1 := by simpa only [d160386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11781 p hg
    simpa only [d160386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11783 (p : Pattern) (guard : d160387 p = 1) : d47686 p ≤ (-1 : Int) + d159763 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160387, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10992 p hg
    simpa only [d160387, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160386 p = 1 := by simpa only [d160387, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11782 p hg
    simpa only [d160387, d47686, d159763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11784 (p : Pattern) (guard : d160388 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160388, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10991 p hg
    simpa only [d160388, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160387 p = 1 := by simpa only [d160388, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11783 p hg
    simpa only [d160388, d47687, d159764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11785 (p : Pattern) (guard : d160389 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160383 p = 1 := by simpa only [d160389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11768 p hg
    simpa only [d160389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160388 p = 1 := by simpa only [d160389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11784 p hg
    simpa only [d160389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11786 (p : Pattern) (guard : d160390 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160389 p = 1 := by simpa only [d160390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11785 p hg
    simpa only [d160390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160325 p = 1 := by simpa only [d160390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11708 p hg
    simpa only [d160390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11787 (p : Pattern) (guard : d160391 p = 1) : d47687 p ≤ (-1 : Int) + d159764 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160390 p = 1 := by simpa only [d160391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11786 p hg
    simpa only [d160391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11003 p hg
    simpa only [d160391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11788 (p : Pattern) (guard : d160392 p = 1) : d47699 p ≤ (-1 : Int) + d159769 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160391 p = 1 := by simpa only [d160392, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11787 p hg
    simpa only [d160392, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160392, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11007 p hg
    simpa only [d160392, d47699, d159769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11789 (p : Pattern) (guard : d160393 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160393, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160393, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160392 p = 1 := by simpa only [d160393, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11788 p hg
    simpa only [d160393, d47700, d159770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11790 (p : Pattern) (guard : d160394 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160393 p = 1 := by simpa only [d160394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11789 p hg
    simpa only [d160394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160330 p = 1 := by simpa only [d160394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11713 p hg
    simpa only [d160394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11791 (p : Pattern) (guard : d160395 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160394 p = 1 := by simpa only [d160395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11790 p hg
    simpa only [d160395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11792 (p : Pattern) (guard : d160396 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160395 p = 1 := by simpa only [d160396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11791 p hg
    simpa only [d160396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11793 (p : Pattern) (guard : d160397 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160396 p = 1 := by simpa only [d160397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11792 p hg
    simpa only [d160397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11794 (p : Pattern) (guard : d160398 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160397 p = 1 := by simpa only [d160398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11793 p hg
    simpa only [d160398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160338 p = 1 := by simpa only [d160398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11721 p hg
    simpa only [d160398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11795 (p : Pattern) (guard : d160399 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160398 p = 1 := by simpa only [d160399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11794 p hg
    simpa only [d160399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11796 (p : Pattern) (guard : d160400 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160330 p = 1 := by simpa only [d160400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11713 p hg
    simpa only [d160400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11797 (p : Pattern) (guard : d160401 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160400 p = 1 := by simpa only [d160401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11796 p hg
    simpa only [d160401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11798 (p : Pattern) (guard : d160402 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160401 p = 1 := by simpa only [d160402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11797 p hg
    simpa only [d160402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11799 (p : Pattern) (guard : d160403 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160402 p = 1 := by simpa only [d160403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11798 p hg
    simpa only [d160403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11800 (p : Pattern) (guard : d160404 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160403 p = 1 := by simpa only [d160404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11799 p hg
    simpa only [d160404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11801 (p : Pattern) (guard : d160405 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160404 p = 1 := by simpa only [d160405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11800 p hg
    simpa only [d160405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11802 (p : Pattern) (guard : d160406 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160399 p = 1 := by simpa only [d160406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11795 p hg
    simpa only [d160406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160405 p = 1 := by simpa only [d160406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11801 p hg
    simpa only [d160406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11803 (p : Pattern) (guard : d160407 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d160378 p = 1 := by simpa only [d160407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11761 p hg
    simpa only [d160407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160406 p = 1 := by simpa only [d160407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11802 p hg
    simpa only [d160407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11804 (p : Pattern) (guard : d160408 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d160369 p = 1 := by simpa only [d160408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11752 p hg
    simpa only [d160408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160407 p = 1 := by simpa only [d160408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11803 p hg
    simpa only [d160408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11805 (p : Pattern) (guard : d160409 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160408 p = 1 := by simpa only [d160409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11804 p hg
    simpa only [d160409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11806 (p : Pattern) (guard : d160410 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160362 p = 1 := by simpa only [d160410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11745 p hg
    simpa only [d160410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11807 (p : Pattern) (guard : d160411 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160364 p = 1 := by simpa only [d160411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11747 p hg
    simpa only [d160411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11808 (p : Pattern) (guard : d160412 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160410 p = 1 := by simpa only [d160412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11806 p hg
    simpa only [d160412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160411 p = 1 := by simpa only [d160412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11807 p hg
    simpa only [d160412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11809 (p : Pattern) (guard : d160413 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160412 p = 1 := by simpa only [d160413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11808 p hg
    simpa only [d160413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11810 (p : Pattern) (guard : d160414 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160413 p = 1 := by simpa only [d160414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11809 p hg
    simpa only [d160414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11811 (p : Pattern) (guard : d160415 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160414 p = 1 := by simpa only [d160415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11810 p hg
    simpa only [d160415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11812 (p : Pattern) (guard : d160416 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160371 p = 1 := by simpa only [d160416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11754 p hg
    simpa only [d160416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11813 (p : Pattern) (guard : d160417 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160374 p = 1 := by simpa only [d160417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11757 p hg
    simpa only [d160417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11814 (p : Pattern) (guard : d160418 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160416 p = 1 := by simpa only [d160418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11812 p hg
    simpa only [d160418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160417 p = 1 := by simpa only [d160418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11813 p hg
    simpa only [d160418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11815 (p : Pattern) (guard : d160419 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160418 p = 1 := by simpa only [d160419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11814 p hg
    simpa only [d160419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11816 (p : Pattern) (guard : d160420 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160419 p = 1 := by simpa only [d160420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11815 p hg
    simpa only [d160420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11817 (p : Pattern) (guard : d160421 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160396 p = 1 := by simpa only [d160421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11792 p hg
    simpa only [d160421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11818 (p : Pattern) (guard : d160422 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160421 p = 1 := by simpa only [d160422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11817 p hg
    simpa only [d160422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160351 p = 1 := by simpa only [d160422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11734 p hg
    simpa only [d160422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11819 (p : Pattern) (guard : d160423 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160422 p = 1 := by simpa only [d160423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11818 p hg
    simpa only [d160423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11820 (p : Pattern) (guard : d160424 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160402 p = 1 := by simpa only [d160424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11798 p hg
    simpa only [d160424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11821 (p : Pattern) (guard : d160425 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160424 p = 1 := by simpa only [d160425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11820 p hg
    simpa only [d160425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11822 (p : Pattern) (guard : d160426 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160425 p = 1 := by simpa only [d160426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11821 p hg
    simpa only [d160426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11823 (p : Pattern) (guard : d160427 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160423 p = 1 := by simpa only [d160427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11819 p hg
    simpa only [d160427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160426 p = 1 := by simpa only [d160427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11822 p hg
    simpa only [d160427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11824 (p : Pattern) (guard : d160428 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d160420 p = 1 := by simpa only [d160428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11816 p hg
    simpa only [d160428, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160427 p = 1 := by simpa only [d160428, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11823 p hg
    simpa only [d160428, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11825 (p : Pattern) (guard : d160429 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d160415 p = 1 := by simpa only [d160429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11811 p hg
    simpa only [d160429, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160428 p = 1 := by simpa only [d160429, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11824 p hg
    simpa only [d160429, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11826 (p : Pattern) (guard : d160430 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160408 p = 1 := by simpa only [d160430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11804 p hg
    simpa only [d160430, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160429 p = 1 := by simpa only [d160430, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11825 p hg
    simpa only [d160430, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11827 (p : Pattern) (guard : d160431 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160409 p = 1 := by simpa only [d160431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11805 p hg
    simpa only [d160431, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160430 p = 1 := by simpa only [d160431, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11826 p hg
    simpa only [d160431, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11828 (p : Pattern) (guard : d160432 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160342 p = 1 := by simpa only [d160432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11725 p hg
    simpa only [d160432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11829 (p : Pattern) (guard : d160433 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160432 p = 1 := by simpa only [d160433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11828 p hg
    simpa only [d160433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11830 (p : Pattern) (guard : d160434 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160433 p = 1 := by simpa only [d160434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11829 p hg
    simpa only [d160434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11831 (p : Pattern) (guard : d160435 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160434 p = 1 := by simpa only [d160435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11830 p hg
    simpa only [d160435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11832 (p : Pattern) (guard : d160436 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160435 p = 1 := by simpa only [d160436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11831 p hg
    simpa only [d160436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11833 (p : Pattern) (guard : d160437 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160347 p = 1 := by simpa only [d160437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11730 p hg
    simpa only [d160437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160436 p = 1 := by simpa only [d160437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11832 p hg
    simpa only [d160437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11834 (p : Pattern) (guard : d160438 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160352 p = 1 := by simpa only [d160438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11735 p hg
    simpa only [d160438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11835 (p : Pattern) (guard : d160439 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160438 p = 1 := by simpa only [d160439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11834 p hg
    simpa only [d160439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11836 (p : Pattern) (guard : d160440 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160439 p = 1 := by simpa only [d160440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11835 p hg
    simpa only [d160440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11837 (p : Pattern) (guard : d160441 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160440 p = 1 := by simpa only [d160441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11836 p hg
    simpa only [d160441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11838 (p : Pattern) (guard : d160442 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160441 p = 1 := by simpa only [d160442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11837 p hg
    simpa only [d160442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11839 (p : Pattern) (guard : d160443 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160436 p = 1 := by simpa only [d160443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11832 p hg
    simpa only [d160443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160442 p = 1 := by simpa only [d160443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11838 p hg
    simpa only [d160443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11840 (p : Pattern) (guard : d160444 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160437 p = 1 := by simpa only [d160444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11833 p hg
    simpa only [d160444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160443 p = 1 := by simpa only [d160444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11839 p hg
    simpa only [d160444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11841 (p : Pattern) (guard : d160445 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160431 p = 1 := by simpa only [d160445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11827 p hg
    simpa only [d160445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160444 p = 1 := by simpa only [d160445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11840 p hg
    simpa only [d160445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11842 (p : Pattern) (guard : d160446 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160445 p = 1 := by simpa only [d160446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11841 p hg
    simpa only [d160446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11843 (p : Pattern) (guard : d160447 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  cases selected : p 50 with
  | false =>
    have hg : d160361 p = 1 := by simpa only [d160447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11744 p hg
    simpa only [d160447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160446 p = 1 := by simpa only [d160447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11842 p hg
    simpa only [d160447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11844 (p : Pattern) (guard : d1102 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1102, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d1102, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1102, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6064 p hg
    simpa only [d1102, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11845 (p : Pattern) (guard : d1103 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11844 p hg
    simpa only [d1103, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d1103, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11846 (p : Pattern) (guard : d160379 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1103 p = 1 := by simpa only [d160379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11845 p hg
    simpa only [d160379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11847 (p : Pattern) (guard : d160380 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160379 p = 1 := by simpa only [d160380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11846 p hg
    simpa only [d160380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11848 (p : Pattern) (guard : d1112 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d1112, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6075 p hg
    simpa only [d1112, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11849 (p : Pattern) (guard : d1113 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11848 p hg
    simpa only [d1113, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d1113, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11850 (p : Pattern) (guard : d160315 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1113 p = 1 := by simpa only [d160315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11849 p hg
    simpa only [d160315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11851 (p : Pattern) (guard : d160316 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160315 p = 1 := by simpa only [d160316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11850 p hg
    simpa only [d160316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11852 (p : Pattern) (guard : d160381 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160380 p = 1 := by simpa only [d160381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11847 p hg
    simpa only [d160381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160316 p = 1 := by simpa only [d160381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11851 p hg
    simpa only [d160381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11853 (p : Pattern) (guard : d160382 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160382, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d160382, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160381 p = 1 := by simpa only [d160382, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11852 p hg
    simpa only [d160382, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11854 (p : Pattern) (guard : d160383 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160383, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d160383, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160382 p = 1 := by simpa only [d160383, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11853 p hg
    simpa only [d160383, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11855 (p : Pattern) (guard : d9452 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5011 p = 1 := by simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6122 p hg
    simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11856 (p : Pattern) (guard : d9453 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d9452 p = 1 := by simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11855 p hg
    simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11857 (p : Pattern) (guard : d9795 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6058 p hg
    simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11856 p hg
    simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11858 (p : Pattern) (guard : d9796 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4686 p hg
    simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4469 p hg
    simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11859 (p : Pattern) (guard : d9797 p = 1) : d47706 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9795 p = 1 := by simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11857 p hg
    simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9796 p = 1 := by simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11858 p hg
    simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11860 (p : Pattern) (guard : d9798 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9797 p = 1 := by simpa only [d9798, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11859 p hg
    simpa only [d9798, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9798, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d9798, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11861 (p : Pattern) (guard : d13024 p = 1) : d47708 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9798 p = 1 := by simpa only [d13024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11860 p hg
    simpa only [d13024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4479 p hg
    simpa only [d13024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11862 (p : Pattern) (guard : d13025 p = 1) : d47735 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d13024 p = 1 := by simpa only [d13025, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11861 p hg
    simpa only [d13025, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13025, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d13025, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11863 (p : Pattern) (guard : d13026 p = 1) : d47736 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d13025 p = 1 := by simpa only [d13026, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11862 p hg
    simpa only [d13026, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13026, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d13026, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11864 (p : Pattern) (guard : d13027 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13027, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d13027, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13026 p = 1 := by simpa only [d13027, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11863 p hg
    simpa only [d13027, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11865 (p : Pattern) (guard : d13028 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13027 p = 1 := by simpa only [d13028, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11864 p hg
    simpa only [d13028, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13028, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d13028, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11866 (p : Pattern) (guard : d160384 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13028 p = 1 := by simpa only [d160384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11865 p hg
    simpa only [d160384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11867 (p : Pattern) (guard : d160385 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160384 p = 1 := by simpa only [d160385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11866 p hg
    simpa only [d160385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11868 (p : Pattern) (guard : d160386 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160316 p = 1 := by simpa only [d160386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11851 p hg
    simpa only [d160386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160385 p = 1 := by simpa only [d160386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11867 p hg
    simpa only [d160386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11869 (p : Pattern) (guard : d160387 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160387, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d160387, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160386 p = 1 := by simpa only [d160387, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11868 p hg
    simpa only [d160387, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11870 (p : Pattern) (guard : d160388 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160388, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d160388, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160387 p = 1 := by simpa only [d160388, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11869 p hg
    simpa only [d160388, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11871 (p : Pattern) (guard : d160389 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160383 p = 1 := by simpa only [d160389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11854 p hg
    simpa only [d160389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160388 p = 1 := by simpa only [d160389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11870 p hg
    simpa only [d160389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11872 (p : Pattern) (guard : d1123 p = 1) : d47737 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11037 p hg
    simpa only [d1123, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6087 p hg
    simpa only [d1123, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11873 (p : Pattern) (guard : d1124 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11872 p hg
    simpa only [d1124, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11039 p hg
    simpa only [d1124, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11874 (p : Pattern) (guard : d160317 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d160317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11873 p hg
    simpa only [d160317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11875 (p : Pattern) (guard : d160318 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160317 p = 1 := by simpa only [d160318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11874 p hg
    simpa only [d160318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11876 (p : Pattern) (guard : d160319 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160316 p = 1 := by simpa only [d160319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11851 p hg
    simpa only [d160319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160318 p = 1 := by simpa only [d160319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11875 p hg
    simpa only [d160319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11877 (p : Pattern) (guard : d160320 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160320, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d160320, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160319 p = 1 := by simpa only [d160320, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11876 p hg
    simpa only [d160320, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11878 (p : Pattern) (guard : d160321 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160321, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d160321, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160320 p = 1 := by simpa only [d160321, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11877 p hg
    simpa only [d160321, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11879 (p : Pattern) (guard : d160322 p = 1) : d47755 p ≤ (-1 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160318 p = 1 := by simpa only [d160322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11875 p hg
    simpa only [d160322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11036 p hg
    simpa only [d160322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11880 (p : Pattern) (guard : d160323 p = 1) : d47756 p ≤ (-1 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160323, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11035 p hg
    simpa only [d160323, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160322 p = 1 := by simpa only [d160323, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11879 p hg
    simpa only [d160323, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11881 (p : Pattern) (guard : d160324 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160324, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11034 p hg
    simpa only [d160324, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160323 p = 1 := by simpa only [d160324, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11880 p hg
    simpa only [d160324, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11882 (p : Pattern) (guard : d160325 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160321 p = 1 := by simpa only [d160325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11878 p hg
    simpa only [d160325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160324 p = 1 := by simpa only [d160325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11881 p hg
    simpa only [d160325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11883 (p : Pattern) (guard : d160390 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160389 p = 1 := by simpa only [d160390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11871 p hg
    simpa only [d160390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160325 p = 1 := by simpa only [d160390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11882 p hg
    simpa only [d160390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11884 (p : Pattern) (guard : d160391 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160390 p = 1 := by simpa only [d160391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11883 p hg
    simpa only [d160391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11885 (p : Pattern) (guard : d160392 p = 1) : d47765 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160391 p = 1 := by simpa only [d160392, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11884 p hg
    simpa only [d160392, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160392, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d160392, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11886 (p : Pattern) (guard : d160393 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160393, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d160393, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160392 p = 1 := by simpa only [d160393, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11885 p hg
    simpa only [d160393, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11887 (p : Pattern) (guard : d160326 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160324 p = 1 := by simpa only [d160326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11881 p hg
    simpa only [d160326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11888 (p : Pattern) (guard : d160327 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160325 p = 1 := by simpa only [d160327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11882 p hg
    simpa only [d160327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160326 p = 1 := by simpa only [d160327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11887 p hg
    simpa only [d160327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11889 (p : Pattern) (guard : d160328 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160327 p = 1 := by simpa only [d160328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11888 p hg
    simpa only [d160328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11890 (p : Pattern) (guard : d160329 p = 1) : d47765 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160328 p = 1 := by simpa only [d160329, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11889 p hg
    simpa only [d160329, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160329, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d160329, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11891 (p : Pattern) (guard : d160330 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160330, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d160330, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160329 p = 1 := by simpa only [d160330, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11890 p hg
    simpa only [d160330, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11892 (p : Pattern) (guard : d160394 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160393 p = 1 := by simpa only [d160394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11886 p hg
    simpa only [d160394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160330 p = 1 := by simpa only [d160394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11891 p hg
    simpa only [d160394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11893 (p : Pattern) (guard : d160395 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160394 p = 1 := by simpa only [d160395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11892 p hg
    simpa only [d160395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11894 (p : Pattern) (guard : d160396 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160395 p = 1 := by simpa only [d160396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11893 p hg
    simpa only [d160396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11895 (p : Pattern) (guard : d160421 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160396 p = 1 := by simpa only [d160421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11894 p hg
    simpa only [d160421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11896 (p : Pattern) (guard : d160331 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160326 p = 1 := by simpa only [d160331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11887 p hg
    simpa only [d160331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11897 (p : Pattern) (guard : d160332 p = 1) : d47757 p ≤ (-1 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160331 p = 1 := by simpa only [d160332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11896 p hg
    simpa only [d160332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11046 p hg
    simpa only [d160332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11898 (p : Pattern) (guard : d160333 p = 1) : d47765 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160332 p = 1 := by simpa only [d160333, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11897 p hg
    simpa only [d160333, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160333, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11050 p hg
    simpa only [d160333, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11899 (p : Pattern) (guard : d160334 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160334, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11033 p hg
    simpa only [d160334, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160333 p = 1 := by simpa only [d160334, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11898 p hg
    simpa only [d160334, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11900 (p : Pattern) (guard : d160335 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160330 p = 1 := by simpa only [d160335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11891 p hg
    simpa only [d160335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160334 p = 1 := by simpa only [d160335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11899 p hg
    simpa only [d160335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11901 (p : Pattern) (guard : d160336 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160335 p = 1 := by simpa only [d160336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11900 p hg
    simpa only [d160336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11902 (p : Pattern) (guard : d160337 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160336 p = 1 := by simpa only [d160337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11901 p hg
    simpa only [d160337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11903 (p : Pattern) (guard : d160351 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160337 p = 1 := by simpa only [d160351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11902 p hg
    simpa only [d160351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11904 (p : Pattern) (guard : d160422 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160421 p = 1 := by simpa only [d160422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11895 p hg
    simpa only [d160422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160351 p = 1 := by simpa only [d160422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11903 p hg
    simpa only [d160422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11905 (p : Pattern) (guard : d160423 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160422 p = 1 := by simpa only [d160423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11904 p hg
    simpa only [d160423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11906 (p : Pattern) (guard : d160400 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160330 p = 1 := by simpa only [d160400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11891 p hg
    simpa only [d160400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11907 (p : Pattern) (guard : d160401 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160400 p = 1 := by simpa only [d160401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11906 p hg
    simpa only [d160401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11908 (p : Pattern) (guard : d160402 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160401 p = 1 := by simpa only [d160402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11907 p hg
    simpa only [d160402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11909 (p : Pattern) (guard : d160424 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160402 p = 1 := by simpa only [d160424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11908 p hg
    simpa only [d160424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11910 (p : Pattern) (guard : d160425 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160424 p = 1 := by simpa only [d160425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11909 p hg
    simpa only [d160425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11911 (p : Pattern) (guard : d160426 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d160425 p = 1 := by simpa only [d160426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11910 p hg
    simpa only [d160426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11912 (p : Pattern) (guard : d160427 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160423 p = 1 := by simpa only [d160427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11905 p hg
    simpa only [d160427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160426 p = 1 := by simpa only [d160427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11911 p hg
    simpa only [d160427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11913 (p : Pattern) (guard : d160448 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160427 p = 1 := by simpa only [d160448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11912 p hg
    simpa only [d160448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11914 (p : Pattern) (guard : d160449 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160449, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160448 p = 1 := by simpa only [d160449, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11913 p hg
    simpa only [d160449, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11915 (p : Pattern) (guard : d160450 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160450, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160450, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160449 p = 1 := by simpa only [d160450, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11914 p hg
    simpa only [d160450, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11916 (p : Pattern) (guard : d160451 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160451, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160450 p = 1 := by simpa only [d160451, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11915 p hg
    simpa only [d160451, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11917 (p : Pattern) (guard : d160339 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160334 p = 1 := by simpa only [d160339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11899 p hg
    simpa only [d160339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11918 (p : Pattern) (guard : d160340 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160339 p = 1 := by simpa only [d160340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11917 p hg
    simpa only [d160340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11919 (p : Pattern) (guard : d160341 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160340 p = 1 := by simpa only [d160341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11918 p hg
    simpa only [d160341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11920 (p : Pattern) (guard : d160352 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160341 p = 1 := by simpa only [d160352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11919 p hg
    simpa only [d160352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11921 (p : Pattern) (guard : d160438 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160352 p = 1 := by simpa only [d160438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11920 p hg
    simpa only [d160438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11922 (p : Pattern) (guard : d160439 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160438 p = 1 := by simpa only [d160439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11921 p hg
    simpa only [d160439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11923 (p : Pattern) (guard : d160440 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160439 p = 1 := by simpa only [d160440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11922 p hg
    simpa only [d160440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11924 (p : Pattern) (guard : d160441 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160440 p = 1 := by simpa only [d160441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11923 p hg
    simpa only [d160441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11925 (p : Pattern) (guard : d160442 p = 1) : d47766 p ≤ (-1 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11032 p hg
    simpa only [d160442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160441 p = 1 := by simpa only [d160442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11924 p hg
    simpa only [d160442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11926 (p : Pattern) (guard : d160452 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160452, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10989 p hg
    simpa only [d160452, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160442 p = 1 := by simpa only [d160452, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11925 p hg
    simpa only [d160452, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11927 (p : Pattern) (guard : d160453 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160452 p = 1 := by simpa only [d160453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11926 p hg
    simpa only [d160453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11928 (p : Pattern) (guard : d160454 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160451 p = 1 := by simpa only [d160454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11916 p hg
    simpa only [d160454, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160453 p = 1 := by simpa only [d160454, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11927 p hg
    simpa only [d160454, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11929 (p : Pattern) (guard : d160455 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160454 p = 1 := by simpa only [d160455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11928 p hg
    simpa only [d160455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11930 (p : Pattern) (guard : d160456 p = 1) : d47767 p ≤ (-1 : Int) + d159775 p := by
  cases selected : p 50 with
  | false =>
    have hg : d160455 p = 1 := by simpa only [d160456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11929 p hg
    simpa only [d160456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11031 p hg
    simpa only [d160456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11931 (p : Pattern) (guard : d160457 p = 1) : d47768 p ≤ (-1 : Int) + d159776 p := by
  cases selected : p 49 with
  | false =>
    have hg : d160447 p = 1 := by simpa only [d160457, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11843 p hg
    simpa only [d160457, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160456 p = 1 := by simpa only [d160457, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11930 p hg
    simpa only [d160457, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11932 (p : Pattern) (guard : d1380 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1380, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d1380, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1099 p = 1 := by simpa only [d1380, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6247 p hg
    simpa only [d1380, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11933 (p : Pattern) (guard : d1381 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1380 p = 1 := by simpa only [d1381, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11932 p hg
    simpa only [d1381, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1100 p = 1 := by simpa only [d1381, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6249 p hg
    simpa only [d1381, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11934 (p : Pattern) (guard : d1382 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1381 p = 1 := by simpa only [d1382, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11933 p hg
    simpa only [d1382, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1382, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6259 p hg
    simpa only [d1382, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11935 (p : Pattern) (guard : d1383 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1382 p = 1 := by simpa only [d1383, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11934 p hg
    simpa only [d1383, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1383, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d1383, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11936 (p : Pattern) (guard : d160458 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1383 p = 1 := by simpa only [d160458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11935 p hg
    simpa only [d160458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11937 (p : Pattern) (guard : d160459 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160458 p = 1 := by simpa only [d160459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11936 p hg
    simpa only [d160459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11938 (p : Pattern) (guard : d1385 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1385, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d1385, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1109 p = 1 := by simpa only [d1385, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6268 p hg
    simpa only [d1385, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11939 (p : Pattern) (guard : d1386 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1385 p = 1 := by simpa only [d1386, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11938 p hg
    simpa only [d1386, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1110 p = 1 := by simpa only [d1386, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6270 p hg
    simpa only [d1386, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11940 (p : Pattern) (guard : d1387 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1386 p = 1 := by simpa only [d1387, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11939 p hg
    simpa only [d1387, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1387, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6279 p hg
    simpa only [d1387, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11941 (p : Pattern) (guard : d1388 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1387 p = 1 := by simpa only [d1388, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11940 p hg
    simpa only [d1388, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1388, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d1388, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11942 (p : Pattern) (guard : d160460 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1388 p = 1 := by simpa only [d160460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11941 p hg
    simpa only [d160460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11943 (p : Pattern) (guard : d160461 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160460 p = 1 := by simpa only [d160461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11942 p hg
    simpa only [d160461, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160461, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160461, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11944 (p : Pattern) (guard : d160462 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160459 p = 1 := by simpa only [d160462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11937 p hg
    simpa only [d160462, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160461 p = 1 := by simpa only [d160462, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11943 p hg
    simpa only [d160462, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11945 (p : Pattern) (guard : d160463 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160463, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d160463, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160462 p = 1 := by simpa only [d160463, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11944 p hg
    simpa only [d160463, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11946 (p : Pattern) (guard : d160464 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160464, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d160464, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160463 p = 1 := by simpa only [d160464, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11945 p hg
    simpa only [d160464, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11947 (p : Pattern) (guard : d9452 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5011 p = 1 := by simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6342 p hg
    simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11948 (p : Pattern) (guard : d9453 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d9452 p = 1 := by simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11947 p hg
    simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11949 (p : Pattern) (guard : d9795 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6243 p hg
    simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11948 p hg
    simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11950 (p : Pattern) (guard : d9796 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4728 p hg
    simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4523 p hg
    simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11951 (p : Pattern) (guard : d9797 p = 1) : d47630 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9795 p = 1 := by simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11949 p hg
    simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9796 p = 1 := by simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11950 p hg
    simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11952 (p : Pattern) (guard : d9798 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9797 p = 1 := by simpa only [d9798, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11951 p hg
    simpa only [d9798, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9798, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4531 p hg
    simpa only [d9798, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11953 (p : Pattern) (guard : d13024 p = 1) : d47652 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9798 p = 1 := by simpa only [d13024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11952 p hg
    simpa only [d13024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4533 p hg
    simpa only [d13024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11954 (p : Pattern) (guard : d13164 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13164, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d13164, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13024 p = 1 := by simpa only [d13164, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11953 p hg
    simpa only [d13164, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11955 (p : Pattern) (guard : d13025 p = 1) : d47797 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d13024 p = 1 := by simpa only [d13025, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11775 p hg
    simpa only [d13025, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13025, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4481 p hg
    simpa only [d13025, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11956 (p : Pattern) (guard : d13165 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d13164 p = 1 := by simpa only [d13165, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11954 p hg
    simpa only [d13165, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13025 p = 1 := by simpa only [d13165, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11955 p hg
    simpa only [d13165, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11957 (p : Pattern) (guard : d9452 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5011 p = 1 := by simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6353 p hg
    simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d9452, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11958 (p : Pattern) (guard : d9453 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d9452 p = 1 := by simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11957 p hg
    simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d9453, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11959 (p : Pattern) (guard : d9795 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6253 p hg
    simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11958 p hg
    simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11960 (p : Pattern) (guard : d9796 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4744 p hg
    simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4541 p hg
    simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11961 (p : Pattern) (guard : d9797 p = 1) : d47634 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9795 p = 1 := by simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11959 p hg
    simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9796 p = 1 := by simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11960 p hg
    simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11962 (p : Pattern) (guard : d9798 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9797 p = 1 := by simpa only [d9798, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11961 p hg
    simpa only [d9798, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9798, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4549 p hg
    simpa only [d9798, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11963 (p : Pattern) (guard : d13024 p = 1) : d47677 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9798 p = 1 := by simpa only [d13024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11962 p hg
    simpa only [d13024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4551 p hg
    simpa only [d13024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11964 (p : Pattern) (guard : d13025 p = 1) : d47682 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d13024 p = 1 := by simpa only [d13025, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11963 p hg
    simpa only [d13025, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13025, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d13025, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11965 (p : Pattern) (guard : d13026 p = 1) : d47683 p ≤ (-1 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d13025 p = 1 := by simpa only [d13026, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11964 p hg
    simpa only [d13026, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13026, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1212 p hg
    simpa only [d13026, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11966 (p : Pattern) (guard : d13166 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d13165 p = 1 := by simpa only [d13166, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11956 p hg
    simpa only [d13166, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13026 p = 1 := by simpa only [d13166, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11965 p hg
    simpa only [d13166, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11967 (p : Pattern) (guard : d13167 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13166 p = 1 := by simpa only [d13167, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11966 p hg
    simpa only [d13167, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13167, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d13167, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11968 (p : Pattern) (guard : d160465 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160465, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d13167 p = 1 := by simpa only [d160465, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11967 p hg
    simpa only [d160465, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11969 (p : Pattern) (guard : d160466 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160465 p = 1 := by simpa only [d160466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11968 p hg
    simpa only [d160466, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160466, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160466, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11970 (p : Pattern) (guard : d160467 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160461 p = 1 := by simpa only [d160467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11943 p hg
    simpa only [d160467, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160466 p = 1 := by simpa only [d160467, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11969 p hg
    simpa only [d160467, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11971 (p : Pattern) (guard : d160468 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160468, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d160468, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160467 p = 1 := by simpa only [d160468, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11970 p hg
    simpa only [d160468, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11972 (p : Pattern) (guard : d160469 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160469, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d160469, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160468 p = 1 := by simpa only [d160469, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11971 p hg
    simpa only [d160469, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11973 (p : Pattern) (guard : d160470 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160464 p = 1 := by simpa only [d160470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11946 p hg
    simpa only [d160470, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160469 p = 1 := by simpa only [d160470, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11972 p hg
    simpa only [d160470, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11974 (p : Pattern) (guard : d1391 p = 1) : d47652 p ≤ (-1 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1391, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11073 p hg
    simpa only [d1391, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1120 p = 1 := by simpa only [d1391, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6289 p hg
    simpa only [d1391, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11975 (p : Pattern) (guard : d1392 p = 1) : d47798 p ≤ (-1 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1391 p = 1 := by simpa only [d1392, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11974 p hg
    simpa only [d1392, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1121 p = 1 := by simpa only [d1392, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6291 p hg
    simpa only [d1392, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11976 (p : Pattern) (guard : d1393 p = 1) : d47799 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1392 p = 1 := by simpa only [d1393, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11975 p hg
    simpa only [d1393, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1393, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare6300 p hg
    simpa only [d1393, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11977 (p : Pattern) (guard : d1394 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1393 p = 1 := by simpa only [d1394, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11976 p hg
    simpa only [d1394, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1394, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11077 p hg
    simpa only [d1394, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11978 (p : Pattern) (guard : d160471 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160471, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1394 p = 1 := by simpa only [d160471, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11977 p hg
    simpa only [d160471, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11979 (p : Pattern) (guard : d160472 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160471 p = 1 := by simpa only [d160472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11978 p hg
    simpa only [d160472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11980 (p : Pattern) (guard : d160473 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160461 p = 1 := by simpa only [d160473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11943 p hg
    simpa only [d160473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160472 p = 1 := by simpa only [d160473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11979 p hg
    simpa only [d160473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11981 (p : Pattern) (guard : d160474 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160474, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d160474, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160473 p = 1 := by simpa only [d160474, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11980 p hg
    simpa only [d160474, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11982 (p : Pattern) (guard : d160475 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160475, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d160475, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160474 p = 1 := by simpa only [d160475, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11981 p hg
    simpa only [d160475, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11983 (p : Pattern) (guard : d160476 p = 1) : d47803 p ≤ (-1 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160472 p = 1 := by simpa only [d160476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11979 p hg
    simpa only [d160476, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160476, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11072 p hg
    simpa only [d160476, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11984 (p : Pattern) (guard : d160477 p = 1) : d47804 p ≤ (-1 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160477, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11071 p hg
    simpa only [d160477, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160476 p = 1 := by simpa only [d160477, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11983 p hg
    simpa only [d160477, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11985 (p : Pattern) (guard : d160478 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160478, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11070 p hg
    simpa only [d160478, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160477 p = 1 := by simpa only [d160478, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11984 p hg
    simpa only [d160478, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11986 (p : Pattern) (guard : d160479 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160475 p = 1 := by simpa only [d160479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11982 p hg
    simpa only [d160479, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160478 p = 1 := by simpa only [d160479, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11985 p hg
    simpa only [d160479, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11987 (p : Pattern) (guard : d160480 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160470 p = 1 := by simpa only [d160480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11973 p hg
    simpa only [d160480, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160479 p = 1 := by simpa only [d160480, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11986 p hg
    simpa only [d160480, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11988 (p : Pattern) (guard : d160481 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160480 p = 1 := by simpa only [d160481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11987 p hg
    simpa only [d160481, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160481, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160481, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11989 (p : Pattern) (guard : d160482 p = 1) : d47807 p ≤ (-1 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160481 p = 1 := by simpa only [d160482, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11988 p hg
    simpa only [d160482, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160482, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d160482, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11990 (p : Pattern) (guard : d160483 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160483, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160483, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160482 p = 1 := by simpa only [d160483, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11989 p hg
    simpa only [d160483, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11991 (p : Pattern) (guard : d160484 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160478 p = 1 := by simpa only [d160484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11985 p hg
    simpa only [d160484, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160484, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160484, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11992 (p : Pattern) (guard : d160485 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160479 p = 1 := by simpa only [d160485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11986 p hg
    simpa only [d160485, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160484 p = 1 := by simpa only [d160485, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11991 p hg
    simpa only [d160485, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11993 (p : Pattern) (guard : d160486 p = 1) : d47805 p ≤ (-1 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160485 p = 1 := by simpa only [d160486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11992 p hg
    simpa only [d160486, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160486, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11084 p hg
    simpa only [d160486, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11994 (p : Pattern) (guard : d160487 p = 1) : d47807 p ≤ (-1 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160486 p = 1 := by simpa only [d160487, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11993 p hg
    simpa only [d160487, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160487, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11088 p hg
    simpa only [d160487, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11995 (p : Pattern) (guard : d160488 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160488, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10990 p hg
    simpa only [d160488, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160487 p = 1 := by simpa only [d160488, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11994 p hg
    simpa only [d160488, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11996 (p : Pattern) (guard : d160489 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160483 p = 1 := by simpa only [d160489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11990 p hg
    simpa only [d160489, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160488 p = 1 := by simpa only [d160489, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11995 p hg
    simpa only [d160489, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11997 (p : Pattern) (guard : d160490 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160489 p = 1 := by simpa only [d160490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11996 p hg
    simpa only [d160490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11998 (p : Pattern) (guard : d160491 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160490 p = 1 := by simpa only [d160491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11997 p hg
    simpa only [d160491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare11999 (p : Pattern) (guard : d160492 p = 1) : d47808 p ≤ (-1 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160491 p = 1 := by simpa only [d160492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11998 p hg
    simpa only [d160492, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160492, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11069 p hg
    simpa only [d160492, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
