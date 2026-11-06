import NetHack.Soko22Hazard87.Compare138
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare34750 (p : Pattern) (guard : d294363 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294362 p = 1 := by simpa only [d294363, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34749 p hg
    simpa only [d294363, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294363, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34045 p hg
    simpa only [d294363, d50036, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34751 (p : Pattern) (guard : d295387 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d295387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294363 p = 1 := by simpa only [d295387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34750 p hg
    simpa only [d295387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34752 (p : Pattern) (guard : d295388 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d295388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295387 p = 1 := by simpa only [d295388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34751 p hg
    simpa only [d295388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34753 (p : Pattern) (guard : d294369 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 159 with
  | false =>
    have hg : d294363 p = 1 := by simpa only [d294369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34750 p hg
    simpa only [d294369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d294369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34754 (p : Pattern) (guard : d295392 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d295387 p = 1 := by simpa only [d295392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34751 p hg
    simpa only [d295392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294369 p = 1 := by simpa only [d295392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34753 p hg
    simpa only [d295392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34755 (p : Pattern) (guard : d295393 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295388 p = 1 := by simpa only [d295393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34752 p hg
    simpa only [d295393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295392 p = 1 := by simpa only [d295393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34754 p hg
    simpa only [d295393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34756 (p : Pattern) (guard : d295394 p = 1) : d50037 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295394, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34013 p hg
    simpa only [d295394, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295393 p = 1 := by simpa only [d295394, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34755 p hg
    simpa only [d295394, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34757 (p : Pattern) (guard : d295395 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295395, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34012 p hg
    simpa only [d295395, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295394 p = 1 := by simpa only [d295395, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34756 p hg
    simpa only [d295395, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34758 (p : Pattern) (guard : d295397 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294369 p = 1 := by simpa only [d295397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34753 p hg
    simpa only [d295397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34014 p hg
    simpa only [d295397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34759 (p : Pattern) (guard : d295398 p = 1) : d50036 p ≤ (0 : Int) + d47803 p := by
  cases selected : p 157 with
  | false =>
    have hg : d295392 p = 1 := by simpa only [d295398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34754 p hg
    simpa only [d295398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295397 p = 1 := by simpa only [d295398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34758 p hg
    simpa only [d295398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34760 (p : Pattern) (guard : d295399 p = 1) : d50037 p ≤ (0 : Int) + d47804 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295399, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34013 p hg
    simpa only [d295399, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295398 p = 1 := by simpa only [d295399, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34759 p hg
    simpa only [d295399, d50037, d47804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34761 (p : Pattern) (guard : d295400 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295400, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34012 p hg
    simpa only [d295400, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295399 p = 1 := by simpa only [d295400, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34760 p hg
    simpa only [d295400, d50038, d47805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34762 (p : Pattern) (guard : d295401 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295395 p = 1 := by simpa only [d295401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34757 p hg
    simpa only [d295401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295400 p = 1 := by simpa only [d295401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34761 p hg
    simpa only [d295401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34763 (p : Pattern) (guard : d295406 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 136 with
  | false =>
    have hg : d295400 p = 1 := by simpa only [d295406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34761 p hg
    simpa only [d295406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d295406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34764 (p : Pattern) (guard : d295407 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295401 p = 1 := by simpa only [d295407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34762 p hg
    simpa only [d295407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295406 p = 1 := by simpa only [d295407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34763 p hg
    simpa only [d295407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34765 (p : Pattern) (guard : d295408 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295407 p = 1 := by simpa only [d295408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34764 p hg
    simpa only [d295408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d295408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34766 (p : Pattern) (guard : d295409 p = 1) : d50040 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295408 p = 1 := by simpa only [d295409, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34765 p hg
    simpa only [d295409, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295409, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34077 p hg
    simpa only [d295409, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34767 (p : Pattern) (guard : d295410 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295410, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d295410, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295409 p = 1 := by simpa only [d295410, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34766 p hg
    simpa only [d295410, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34768 (p : Pattern) (guard : d295415 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 135 with
  | false =>
    have hg : d295406 p = 1 := by simpa only [d295415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34763 p hg
    simpa only [d295415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d295415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34769 (p : Pattern) (guard : d295416 p = 1) : d50038 p ≤ (0 : Int) + d47805 p := by
  cases selected : p 119 with
  | false =>
    have hg : d295415 p = 1 := by simpa only [d295416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34768 p hg
    simpa only [d295416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34073 p hg
    simpa only [d295416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34770 (p : Pattern) (guard : d295417 p = 1) : d50040 p ≤ (0 : Int) + d47807 p := by
  cases selected : p 116 with
  | false =>
    have hg : d295416 p = 1 := by simpa only [d295417, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34769 p hg
    simpa only [d295417, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295417, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34077 p hg
    simpa only [d295417, d50040, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34771 (p : Pattern) (guard : d295418 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295418, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33826 p hg
    simpa only [d295418, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295417 p = 1 := by simpa only [d295418, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34770 p hg
    simpa only [d295418, d50041, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34772 (p : Pattern) (guard : d295419 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295410 p = 1 := by simpa only [d295419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34767 p hg
    simpa only [d295419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295418 p = 1 := by simpa only [d295419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34771 p hg
    simpa only [d295419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34773 (p : Pattern) (guard : d295420 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295419 p = 1 := by simpa only [d295420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34772 p hg
    simpa only [d295420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34774 (p : Pattern) (guard : d295421 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295420 p = 1 := by simpa only [d295421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34773 p hg
    simpa only [d295421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34775 (p : Pattern) (guard : d295422 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295421 p = 1 := by simpa only [d295422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34774 p hg
    simpa only [d295422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34776 (p : Pattern) (guard : d295445 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d295418 p = 1 := by simpa only [d295445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34771 p hg
    simpa only [d295445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34777 (p : Pattern) (guard : d295446 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 96 with
  | false =>
    have hg : d295445 p = 1 := by simpa only [d295446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34776 p hg
    simpa only [d295446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34778 (p : Pattern) (guard : d295447 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 95 with
  | false =>
    have hg : d295446 p = 1 := by simpa only [d295447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34777 p hg
    simpa only [d295447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34779 (p : Pattern) (guard : d295448 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 93 with
  | false =>
    have hg : d295447 p = 1 := by simpa only [d295448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34778 p hg
    simpa only [d295448, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295448, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295448, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34780 (p : Pattern) (guard : d295771 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 91 with
  | false =>
    have hg : d295422 p = 1 := by simpa only [d295771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34775 p hg
    simpa only [d295771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295448 p = 1 := by simpa only [d295771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34779 p hg
    simpa only [d295771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34781 (p : Pattern) (guard : d295772 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295771 p = 1 := by simpa only [d295772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34780 p hg
    simpa only [d295772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34782 (p : Pattern) (guard : d295773 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 89 with
  | false =>
    have hg : d295772 p = 1 := by simpa only [d295773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34781 p hg
    simpa only [d295773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34783 (p : Pattern) (guard : d295774 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295773 p = 1 := by simpa only [d295774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34782 p hg
    simpa only [d295774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34784 (p : Pattern) (guard : d295775 p = 1) : d50041 p ≤ (0 : Int) + d47808 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34011 p hg
    simpa only [d295775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295774 p = 1 := by simpa only [d295775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34783 p hg
    simpa only [d295775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34785 (p : Pattern) (guard : d295776 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295776, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33824 p hg
    simpa only [d295776, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295775 p = 1 := by simpa only [d295776, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34784 p hg
    simpa only [d295776, d50042, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34786 (p : Pattern) (guard : d295777 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d295777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295776 p = 1 := by simpa only [d295777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34785 p hg
    simpa only [d295777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34787 (p : Pattern) (guard : d295778 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 69 with
  | false =>
    have hg : d295777 p = 1 := by simpa only [d295778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34786 p hg
    simpa only [d295778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d295778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34788 (p : Pattern) (guard : d295779 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 51 with
  | false =>
    have hg : d295778 p = 1 := by simpa only [d295779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34787 p hg
    simpa only [d295779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d295779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34789 (p : Pattern) (guard : d295780 p = 1) : d50042 p ≤ (0 : Int) + d47809 p := by
  cases selected : p 50 with
  | false =>
    have hg : d295779 p = 1 := by simpa only [d295780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34788 p hg
    simpa only [d295780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34010 p hg
    simpa only [d295780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34790 (p : Pattern) (guard : d295781 p = 1) : d50100 p ≤ (0 : Int) + d47865 p := by
  cases selected : p 49 with
  | false =>
    have hg : d295780 p = 1 := by simpa only [d295781, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34789 p hg
    simpa only [d295781, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295781, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34102 p hg
    simpa only [d295781, d50100, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34791 (p : Pattern) (guard : d295782 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 48 with
  | false =>
    have hg : d295770 p = 1 := by simpa only [d295782, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34727 p hg
    simpa only [d295782, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295781 p = 1 := by simpa only [d295782, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34790 p hg
    simpa only [d295782, d50101, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34792 (p : Pattern) (guard : d295783 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295782 p = 1 := by simpa only [d295783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34791 p hg
    simpa only [d295783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34793 (p : Pattern) (guard : d295784 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295783 p = 1 := by simpa only [d295784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34792 p hg
    simpa only [d295784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34794 (p : Pattern) (guard : d295785 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295784 p = 1 := by simpa only [d295785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34793 p hg
    simpa only [d295785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34795 (p : Pattern) (guard : d295786 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295785 p = 1 := by simpa only [d295786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34794 p hg
    simpa only [d295786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34796 (p : Pattern) (guard : d295787 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295786 p = 1 := by simpa only [d295787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34795 p hg
    simpa only [d295787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34797 (p : Pattern) (guard : d295788 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295787 p = 1 := by simpa only [d295788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34796 p hg
    simpa only [d295788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34798 (p : Pattern) (guard : d295789 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295788 p = 1 := by simpa only [d295789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34797 p hg
    simpa only [d295789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34799 (p : Pattern) (guard : d295790 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295789 p = 1 := by simpa only [d295790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34798 p hg
    simpa only [d295790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34800 (p : Pattern) (guard : d295791 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295790 p = 1 := by simpa only [d295791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34799 p hg
    simpa only [d295791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34801 (p : Pattern) (guard : d295792 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d295792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295791 p = 1 := by simpa only [d295792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34800 p hg
    simpa only [d295792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34802 (p : Pattern) (guard : d295793 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d295762 p = 1 := by simpa only [d295793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34591 p hg
    simpa only [d295793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d295792 p = 1 := by simpa only [d295793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34801 p hg
    simpa only [d295793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34803 (p : Pattern) (guard : d295794 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 260 with
  | false =>
    have hg : d295793 p = 1 := by simpa only [d295794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34802 p hg
    simpa only [d295794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34804 (p : Pattern) (guard : d295795 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 259 with
  | false =>
    have hg : d295794 p = 1 := by simpa only [d295795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34803 p hg
    simpa only [d295795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34805 (p : Pattern) (guard : d295796 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 258 with
  | false =>
    have hg : d295795 p = 1 := by simpa only [d295796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34804 p hg
    simpa only [d295796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34806 (p : Pattern) (guard : d295797 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 257 with
  | false =>
    have hg : d295796 p = 1 := by simpa only [d295797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34805 p hg
    simpa only [d295797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34807 (p : Pattern) (guard : d295798 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 256 with
  | false =>
    have hg : d295797 p = 1 := by simpa only [d295798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34806 p hg
    simpa only [d295798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34808 (p : Pattern) (guard : d295799 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 255 with
  | false =>
    have hg : d295798 p = 1 := by simpa only [d295799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34807 p hg
    simpa only [d295799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34809 (p : Pattern) (guard : d295800 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 254 with
  | false =>
    have hg : d295799 p = 1 := by simpa only [d295800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34808 p hg
    simpa only [d295800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34810 (p : Pattern) (guard : d295801 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 253 with
  | false =>
    have hg : d295800 p = 1 := by simpa only [d295801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34809 p hg
    simpa only [d295801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34811 (p : Pattern) (guard : d295802 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 252 with
  | false =>
    have hg : d295801 p = 1 := by simpa only [d295802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34810 p hg
    simpa only [d295802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34812 (p : Pattern) (guard : d295803 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 251 with
  | false =>
    have hg : d295802 p = 1 := by simpa only [d295803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34811 p hg
    simpa only [d295803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34813 (p : Pattern) (guard : d295804 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 250 with
  | false =>
    have hg : d295803 p = 1 := by simpa only [d295804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34812 p hg
    simpa only [d295804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34814 (p : Pattern) (guard : d295805 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 249 with
  | false =>
    have hg : d295804 p = 1 := by simpa only [d295805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34813 p hg
    simpa only [d295805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34815 (p : Pattern) (guard : d295806 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 245 with
  | false =>
    have hg : d295805 p = 1 := by simpa only [d295806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34814 p hg
    simpa only [d295806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34816 (p : Pattern) (guard : d295807 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 200 with
  | false =>
    have hg : d295806 p = 1 := by simpa only [d295807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34815 p hg
    simpa only [d295807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34817 (p : Pattern) (guard : d295808 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 199 with
  | false =>
    have hg : d295807 p = 1 := by simpa only [d295808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34816 p hg
    simpa only [d295808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34818 (p : Pattern) (guard : d295809 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 186 with
  | false =>
    have hg : d295808 p = 1 := by simpa only [d295809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34817 p hg
    simpa only [d295809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34819 (p : Pattern) (guard : d295810 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 185 with
  | false =>
    have hg : d295809 p = 1 := by simpa only [d295810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34818 p hg
    simpa only [d295810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34820 (p : Pattern) (guard : d295811 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 184 with
  | false =>
    have hg : d295810 p = 1 := by simpa only [d295811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34819 p hg
    simpa only [d295811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34821 (p : Pattern) (guard : d295812 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 181 with
  | false =>
    have hg : d295811 p = 1 := by simpa only [d295812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34820 p hg
    simpa only [d295812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34822 (p : Pattern) (guard : d295813 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 177 with
  | false =>
    have hg : d295812 p = 1 := by simpa only [d295813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34821 p hg
    simpa only [d295813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34823 (p : Pattern) (guard : d295814 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 164 with
  | false =>
    have hg : d295813 p = 1 := by simpa only [d295814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34822 p hg
    simpa only [d295814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34824 (p : Pattern) (guard : d295815 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 156 with
  | false =>
    have hg : d295814 p = 1 := by simpa only [d295815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34823 p hg
    simpa only [d295815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34825 (p : Pattern) (guard : d295816 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 155 with
  | false =>
    have hg : d295815 p = 1 := by simpa only [d295816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34824 p hg
    simpa only [d295816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34826 (p : Pattern) (guard : d295817 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 134 with
  | false =>
    have hg : d295816 p = 1 := by simpa only [d295817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34825 p hg
    simpa only [d295817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34827 (p : Pattern) (guard : d295818 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 133 with
  | false =>
    have hg : d295817 p = 1 := by simpa only [d295818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34826 p hg
    simpa only [d295818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34828 (p : Pattern) (guard : d295819 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 120 with
  | false =>
    have hg : d295818 p = 1 := by simpa only [d295819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34827 p hg
    simpa only [d295819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34829 (p : Pattern) (guard : d295820 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 118 with
  | false =>
    have hg : d295819 p = 1 := by simpa only [d295820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34828 p hg
    simpa only [d295820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34830 (p : Pattern) (guard : d295821 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 114 with
  | false =>
    have hg : d295820 p = 1 := by simpa only [d295821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34829 p hg
    simpa only [d295821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34831 (p : Pattern) (guard : d295822 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 111 with
  | false =>
    have hg : d295821 p = 1 := by simpa only [d295822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34830 p hg
    simpa only [d295822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34832 (p : Pattern) (guard : d295823 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 98 with
  | false =>
    have hg : d295822 p = 1 := by simpa only [d295823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34831 p hg
    simpa only [d295823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34833 (p : Pattern) (guard : d295824 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 97 with
  | false =>
    have hg : d295823 p = 1 := by simpa only [d295824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34832 p hg
    simpa only [d295824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34834 (p : Pattern) (guard : d295825 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 94 with
  | false =>
    have hg : d295824 p = 1 := by simpa only [d295825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34833 p hg
    simpa only [d295825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34835 (p : Pattern) (guard : d295826 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 76 with
  | false =>
    have hg : d295825 p = 1 := by simpa only [d295826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34834 p hg
    simpa only [d295826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34836 (p : Pattern) (guard : d295827 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 67 with
  | false =>
    have hg : d295826 p = 1 := by simpa only [d295827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34835 p hg
    simpa only [d295827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34837 (p : Pattern) (guard : d295828 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 52 with
  | false =>
    have hg : d295827 p = 1 := by simpa only [d295828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34836 p hg
    simpa only [d295828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34838 (p : Pattern) (guard : d295829 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 47 with
  | false =>
    have hg : d295828 p = 1 := by simpa only [d295829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34837 p hg
    simpa only [d295829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34839 (p : Pattern) (guard : d295830 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 46 with
  | false =>
    have hg : d295829 p = 1 := by simpa only [d295830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34838 p hg
    simpa only [d295830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34840 (p : Pattern) (guard : d295831 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 45 with
  | false =>
    have hg : d295830 p = 1 := by simpa only [d295831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34839 p hg
    simpa only [d295831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34841 (p : Pattern) (guard : d295832 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 30 with
  | false =>
    have hg : d295831 p = 1 := by simpa only [d295832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34840 p hg
    simpa only [d295832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34842 (p : Pattern) (guard : d295833 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 29 with
  | false =>
    have hg : d295832 p = 1 := by simpa only [d295833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34841 p hg
    simpa only [d295833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34843 (p : Pattern) (guard : d295834 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 28 with
  | false =>
    have hg : d295833 p = 1 := by simpa only [d295834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34842 p hg
    simpa only [d295834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34844 (p : Pattern) (guard : d295835 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 27 with
  | false =>
    have hg : d295834 p = 1 := by simpa only [d295835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34843 p hg
    simpa only [d295835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34845 (p : Pattern) (guard : d295836 p = 1) : d50101 p ≤ (0 : Int) + d47866 p := by
  cases selected : p 25 with
  | false =>
    have hg : d295835 p = 1 := by simpa only [d295836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34844 p hg
    simpa only [d295836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d295836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare33822 p hg
    simpa only [d295836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34846 (p : Pattern) (guard : d0 p = 1) : d50101 p ≤ (-1 : Int) + d51138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34847 (p : Pattern) (guard : d0 p = 1) : d50101 p ≤ (-2 : Int) + d51138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34848 (p : Pattern) (guard : d0 p = 1) : d50101 p ≤ (-1 : Int) + d50493 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34849 (p : Pattern) (guard : d0 p = 1) : d50101 p ≤ (-2 : Int) + d50493 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34850 (p : Pattern) (guard : d0 p = 1) : d50101 p ≤ (-1 : Int) + d300401 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34851 (p : Pattern) (guard : d0 p = 1) : d50101 p ≤ (-2 : Int) + d300401 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34852 (p : Pattern) (guard : d0 p = 1) : d50101 p ≤ (-1 : Int) + d51635 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34853 (p : Pattern) (guard : d0 p = 1) : d50101 p ≤ (-2 : Int) + d51635 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34854 (p : Pattern) (guard : d0 p = 1) : d50493 p ≤ (-1 : Int) + d51635 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34855 (p : Pattern) (guard : d0 p = 1) : d50493 p ≤ (-2 : Int) + d51635 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34856 (p : Pattern) (guard : d0 p = 1) : d50493 p ≤ (-1 : Int) + d50823 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34857 (p : Pattern) (guard : d0 p = 1) : d50493 p ≤ (-2 : Int) + d50823 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34858 (p : Pattern) (guard : d0 p = 1) : d50493 p ≤ (-1 : Int) + d50101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34859 (p : Pattern) (guard : d0 p = 1) : d50493 p ≤ (-2 : Int) + d50101 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34860 (p : Pattern) (guard : d0 p = 1) : d50493 p ≤ (3 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34861 (p : Pattern) (guard : d0 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34862 (p : Pattern) (guard : d0 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34863 (p : Pattern) (guard : d0 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34864 (p : Pattern) (guard : d0 p = 1) : d50266 p ≤ (3 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34865 (p : Pattern) (guard : d0 p = 1) : d50270 p ≤ (3 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34866 (p : Pattern) (guard : d0 p = 1) : d50216 p ≤ (3 : Int) + d47681 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34867 (p : Pattern) (guard : d0 p = 1) : d50219 p ≤ (3 : Int) + d47655 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34868 (p : Pattern) (guard : d0 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34869 (p : Pattern) (guard : d16 p = 1) : d47617 p ≤ (3 : Int) + d47617 p := by
  omega
theorem compare34870 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (3 : Int) + d47617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34871 (p : Pattern) (guard : d17 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34869 p hg
    simpa only [d17, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, d50119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34870 p hg
    simpa only [d17, d50119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34872 (p : Pattern) (guard : d38813 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34871 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34873 (p : Pattern) (guard : d257183 p = 1) : d50119 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d38813 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34872 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34868 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34874 (p : Pattern) (guard : d0 p = 1) : d50121 p ≤ (3 : Int) + d47617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34875 (p : Pattern) (guard : d257184 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257183 p = 1 := by simpa only [d257184, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34873 p hg
    simpa only [d257184, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257184, d50122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34874 p hg
    simpa only [d257184, d50122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34876 (p : Pattern) (guard : d0 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34877 (p : Pattern) (guard : d257185 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257184 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34875 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34878 (p : Pattern) (guard : d257186 p = 1) : d50122 p ≤ (3 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257185 p = 1 := by simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34877 p hg
    simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34876 p hg
    simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34879 (p : Pattern) (guard : d0 p = 1) : d50201 p ≤ (3 : Int) + d47618 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34880 (p : Pattern) (guard : d257187 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d257186 p = 1 := by simpa only [d257187, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34878 p hg
    simpa only [d257187, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257187, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34879 p hg
    simpa only [d257187, d50202, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34881 (p : Pattern) (guard : d0 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34882 (p : Pattern) (guard : d257188 p = 1) : d50202 p ≤ (3 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257187 p = 1 := by simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34880 p hg
    simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34881 p hg
    simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34883 (p : Pattern) (guard : d0 p = 1) : d50180 p ≤ (3 : Int) + d47659 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34884 (p : Pattern) (guard : d257189 p = 1) : d50220 p ≤ (3 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d257188 p = 1 := by simpa only [d257189, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34882 p hg
    simpa only [d257189, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257189, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d257189, d50220, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34885 (p : Pattern) (guard : d0 p = 1) : d50184 p ≤ (3 : Int) + d47662 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34886 (p : Pattern) (guard : d257190 p = 1) : d50221 p ≤ (3 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d257189 p = 1 := by simpa only [d257190, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34884 p hg
    simpa only [d257190, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257190, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d257190, d50221, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34887 (p : Pattern) (guard : d257191 p = 1) : d50222 p ≤ (3 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257191, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d257191, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257190 p = 1 := by simpa only [d257191, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34886 p hg
    simpa only [d257191, d50222, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34888 (p : Pattern) (guard : d0 p = 1) : d50225 p ≤ (3 : Int) + d47684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34889 (p : Pattern) (guard : d257192 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d257191 p = 1 := by simpa only [d257192, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34887 p hg
    simpa only [d257192, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257192, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d257192, d50226, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34890 (p : Pattern) (guard : d0 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34891 (p : Pattern) (guard : d257193 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d257192 p = 1 := by simpa only [d257193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34889 p hg
    simpa only [d257193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d257193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34892 (p : Pattern) (guard : d257194 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d257193 p = 1 := by simpa only [d257194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34891 p hg
    simpa only [d257194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d257194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34893 (p : Pattern) (guard : d257195 p = 1) : d50226 p ≤ (3 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d257194 p = 1 := by simpa only [d257195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34892 p hg
    simpa only [d257195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34890 p hg
    simpa only [d257195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34894 (p : Pattern) (guard : d257196 p = 1) : d50227 p ≤ (3 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257196, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34866 p hg
    simpa only [d257196, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257195 p = 1 := by simpa only [d257196, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34893 p hg
    simpa only [d257196, d50227, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34895 (p : Pattern) (guard : d257197 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257197, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34865 p hg
    simpa only [d257197, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257196 p = 1 := by simpa only [d257197, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34894 p hg
    simpa only [d257197, d50271, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34896 (p : Pattern) (guard : d0 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34897 (p : Pattern) (guard : d257198 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d257197 p = 1 := by simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34895 p hg
    simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34898 (p : Pattern) (guard : d257199 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d257198 p = 1 := by simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34897 p hg
    simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34899 (p : Pattern) (guard : d257200 p = 1) : d50271 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d257199 p = 1 := by simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34898 p hg
    simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34900 (p : Pattern) (guard : d0 p = 1) : d50249 p ≤ (3 : Int) + d47698 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34901 (p : Pattern) (guard : d257201 p = 1) : d50272 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d257200 p = 1 := by simpa only [d257201, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34899 p hg
    simpa only [d257201, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257201, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d257201, d50272, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34902 (p : Pattern) (guard : d257202 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257202, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34864 p hg
    simpa only [d257202, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257201 p = 1 := by simpa only [d257202, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34901 p hg
    simpa only [d257202, d50273, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34903 (p : Pattern) (guard : d257203 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d257202 p = 1 := by simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34902 p hg
    simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34904 (p : Pattern) (guard : d257204 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d257203 p = 1 := by simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34903 p hg
    simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34905 (p : Pattern) (guard : d257205 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d257204 p = 1 := by simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34904 p hg
    simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34906 (p : Pattern) (guard : d257206 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257205 p = 1 := by simpa only [d257206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34905 p hg
    simpa only [d257206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34907 (p : Pattern) (guard : d257207 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d257206 p = 1 := by simpa only [d257207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34906 p hg
    simpa only [d257207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34908 (p : Pattern) (guard : d257208 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d257207 p = 1 := by simpa only [d257208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34907 p hg
    simpa only [d257208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34909 (p : Pattern) (guard : d257209 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257208 p = 1 := by simpa only [d257209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34908 p hg
    simpa only [d257209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34910 (p : Pattern) (guard : d257210 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257209 p = 1 := by simpa only [d257210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34909 p hg
    simpa only [d257210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34911 (p : Pattern) (guard : d257211 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257210 p = 1 := by simpa only [d257211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34910 p hg
    simpa only [d257211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34912 (p : Pattern) (guard : d257212 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257212, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257212, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257211 p = 1 := by simpa only [d257212, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34911 p hg
    simpa only [d257212, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34913 (p : Pattern) (guard : d0 p = 1) : d50238 p ≤ (3 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34914 (p : Pattern) (guard : d0 p = 1) : d50247 p ≤ (3 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34915 (p : Pattern) (guard : d257197 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257197, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d257197, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257196 p = 1 := by simpa only [d257197, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34894 p hg
    simpa only [d257197, d50248, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34916 (p : Pattern) (guard : d0 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34917 (p : Pattern) (guard : d257198 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d257197 p = 1 := by simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34915 p hg
    simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34918 (p : Pattern) (guard : d257199 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d257198 p = 1 := by simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34917 p hg
    simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34919 (p : Pattern) (guard : d257200 p = 1) : d50248 p ≤ (3 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d257199 p = 1 := by simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34918 p hg
    simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34916 p hg
    simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34920 (p : Pattern) (guard : d257201 p = 1) : d50250 p ≤ (3 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d257200 p = 1 := by simpa only [d257201, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34919 p hg
    simpa only [d257201, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257201, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d257201, d50250, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34921 (p : Pattern) (guard : d257202 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257202, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d257202, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257201 p = 1 := by simpa only [d257202, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34920 p hg
    simpa only [d257202, d50251, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34922 (p : Pattern) (guard : d257203 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d257202 p = 1 := by simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34921 p hg
    simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34923 (p : Pattern) (guard : d257204 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d257203 p = 1 := by simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34922 p hg
    simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34924 (p : Pattern) (guard : d257205 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d257204 p = 1 := by simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34923 p hg
    simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34925 (p : Pattern) (guard : d257206 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257205 p = 1 := by simpa only [d257206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34924 p hg
    simpa only [d257206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34926 (p : Pattern) (guard : d257207 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d257206 p = 1 := by simpa only [d257207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34925 p hg
    simpa only [d257207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34927 (p : Pattern) (guard : d257208 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d257207 p = 1 := by simpa only [d257208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34926 p hg
    simpa only [d257208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34928 (p : Pattern) (guard : d257209 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257208 p = 1 := by simpa only [d257209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34927 p hg
    simpa only [d257209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34929 (p : Pattern) (guard : d257210 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257209 p = 1 := by simpa only [d257210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34928 p hg
    simpa only [d257210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34930 (p : Pattern) (guard : d257211 p = 1) : d50251 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257210 p = 1 := by simpa only [d257211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34929 p hg
    simpa only [d257211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34931 (p : Pattern) (guard : d257213 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d257205 p = 1 := by simpa only [d257213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34905 p hg
    simpa only [d257213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34932 (p : Pattern) (guard : d257214 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d257213 p = 1 := by simpa only [d257214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34931 p hg
    simpa only [d257214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34933 (p : Pattern) (guard : d257215 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d257214 p = 1 := by simpa only [d257215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34932 p hg
    simpa only [d257215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34934 (p : Pattern) (guard : d257216 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257215 p = 1 := by simpa only [d257216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34933 p hg
    simpa only [d257216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34935 (p : Pattern) (guard : d257217 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257216 p = 1 := by simpa only [d257217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34934 p hg
    simpa only [d257217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34936 (p : Pattern) (guard : d257218 p = 1) : d50273 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34863 p hg
    simpa only [d257218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257217 p = 1 := by simpa only [d257218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34935 p hg
    simpa only [d257218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34937 (p : Pattern) (guard : d257219 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d257211 p = 1 := by simpa only [d257219, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34930 p hg
    simpa only [d257219, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257218 p = 1 := by simpa only [d257219, d50274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34936 p hg
    simpa only [d257219, d50274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34938 (p : Pattern) (guard : d257220 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d257212 p = 1 := by simpa only [d257220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34912 p hg
    simpa only [d257220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257219 p = 1 := by simpa only [d257220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34937 p hg
    simpa only [d257220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34939 (p : Pattern) (guard : d257221 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d257220 p = 1 := by simpa only [d257221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34938 p hg
    simpa only [d257221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d257221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34940 (p : Pattern) (guard : d257222 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d257221 p = 1 := by simpa only [d257222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34939 p hg
    simpa only [d257222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d257222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34941 (p : Pattern) (guard : d257223 p = 1) : d50274 p ≤ (3 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d257223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257222 p = 1 := by simpa only [d257223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34940 p hg
    simpa only [d257223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34942 (p : Pattern) (guard : d0 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34943 (p : Pattern) (guard : d0 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34944 (p : Pattern) (guard : d0 p = 1) : d50376 p ≤ (3 : Int) + d47763 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34945 (p : Pattern) (guard : d0 p = 1) : d50384 p ≤ (3 : Int) + d47746 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34946 (p : Pattern) (guard : d0 p = 1) : d50358 p ≤ (3 : Int) + d47751 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34947 (p : Pattern) (guard : d0 p = 1) : d50361 p ≤ (3 : Int) + d47734 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34948 (p : Pattern) (guard : d0 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34949 (p : Pattern) (guard : d16 p = 1) : d47706 p ≤ (3 : Int) + d47706 p := by
  omega
theorem compare34950 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (3 : Int) + d47706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34951 (p : Pattern) (guard : d17 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d16 p = 1 := by simpa only [d17, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34949 p hg
    simpa only [d17, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d17, d50288, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34950 p hg
    simpa only [d17, d50288, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34952 (p : Pattern) (guard : d38813 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34951 p hg
    simpa only [d38813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34953 (p : Pattern) (guard : d257183 p = 1) : d50288 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d38813 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34952 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34948 p hg
    simpa only [d257183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34954 (p : Pattern) (guard : d0 p = 1) : d50290 p ≤ (3 : Int) + d47706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34955 (p : Pattern) (guard : d257184 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d257183 p = 1 := by simpa only [d257184, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34953 p hg
    simpa only [d257184, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257184, d50291, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34954 p hg
    simpa only [d257184, d50291, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34956 (p : Pattern) (guard : d0 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34957 (p : Pattern) (guard : d257185 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d257184 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34955 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d257185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34958 (p : Pattern) (guard : d257186 p = 1) : d50291 p ≤ (3 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257185 p = 1 := by simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34957 p hg
    simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34956 p hg
    simpa only [d257186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34959 (p : Pattern) (guard : d0 p = 1) : d50346 p ≤ (3 : Int) + d47707 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34960 (p : Pattern) (guard : d257187 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d257186 p = 1 := by simpa only [d257187, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34958 p hg
    simpa only [d257187, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257187, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34959 p hg
    simpa only [d257187, d50347, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34961 (p : Pattern) (guard : d0 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34962 (p : Pattern) (guard : d257188 p = 1) : d50347 p ≤ (3 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d257187 p = 1 := by simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34960 p hg
    simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34961 p hg
    simpa only [d257188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34963 (p : Pattern) (guard : d0 p = 1) : d50183 p ≤ (3 : Int) + d47661 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34964 (p : Pattern) (guard : d257189 p = 1) : d50362 p ≤ (3 : Int) + d47735 p := by
  cases selected : p 163 with
  | false =>
    have hg : d257188 p = 1 := by simpa only [d257189, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34962 p hg
    simpa only [d257189, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257189, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34963 p hg
    simpa only [d257189, d50362, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34965 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (3 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34966 (p : Pattern) (guard : d257190 p = 1) : d50363 p ≤ (3 : Int) + d47736 p := by
  cases selected : p 162 with
  | false =>
    have hg : d257189 p = 1 := by simpa only [d257190, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34964 p hg
    simpa only [d257190, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257190, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d257190, d50363, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34967 (p : Pattern) (guard : d257191 p = 1) : d50364 p ≤ (3 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257191, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34947 p hg
    simpa only [d257191, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257190 p = 1 := by simpa only [d257191, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34966 p hg
    simpa only [d257191, d50364, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34968 (p : Pattern) (guard : d0 p = 1) : d50367 p ≤ (3 : Int) + d47754 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34969 (p : Pattern) (guard : d257192 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d257191 p = 1 := by simpa only [d257192, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34967 p hg
    simpa only [d257192, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257192, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34968 p hg
    simpa only [d257192, d50368, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34970 (p : Pattern) (guard : d0 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34971 (p : Pattern) (guard : d257193 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d257192 p = 1 := by simpa only [d257193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34969 p hg
    simpa only [d257193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d257193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34972 (p : Pattern) (guard : d257194 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d257193 p = 1 := by simpa only [d257194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34971 p hg
    simpa only [d257194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d257194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34973 (p : Pattern) (guard : d257195 p = 1) : d50368 p ≤ (3 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d257194 p = 1 := by simpa only [d257195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34972 p hg
    simpa only [d257195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d257195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34974 (p : Pattern) (guard : d257196 p = 1) : d50369 p ≤ (3 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257196, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d257196, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257195 p = 1 := by simpa only [d257196, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34973 p hg
    simpa only [d257196, d50369, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34975 (p : Pattern) (guard : d257197 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257197, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34945 p hg
    simpa only [d257197, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257196 p = 1 := by simpa only [d257197, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34974 p hg
    simpa only [d257197, d50385, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34976 (p : Pattern) (guard : d0 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34977 (p : Pattern) (guard : d257198 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d257197 p = 1 := by simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34975 p hg
    simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d257198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34978 (p : Pattern) (guard : d257199 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d257198 p = 1 := by simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34977 p hg
    simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d257199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34979 (p : Pattern) (guard : d257200 p = 1) : d50385 p ≤ (3 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d257199 p = 1 := by simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34978 p hg
    simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d257200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34980 (p : Pattern) (guard : d0 p = 1) : d50386 p ≤ (3 : Int) + d47764 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34981 (p : Pattern) (guard : d257201 p = 1) : d50387 p ≤ (3 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d257200 p = 1 := by simpa only [d257201, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34979 p hg
    simpa only [d257201, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257201, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d257201, d50387, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34982 (p : Pattern) (guard : d257202 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257202, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34944 p hg
    simpa only [d257202, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257201 p = 1 := by simpa only [d257202, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34981 p hg
    simpa only [d257202, d50388, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34983 (p : Pattern) (guard : d257203 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d257202 p = 1 := by simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34982 p hg
    simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d257203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34984 (p : Pattern) (guard : d257204 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d257203 p = 1 := by simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34983 p hg
    simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d257204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34985 (p : Pattern) (guard : d257205 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d257204 p = 1 := by simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34984 p hg
    simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d257205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34986 (p : Pattern) (guard : d257213 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d257205 p = 1 := by simpa only [d257213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34985 p hg
    simpa only [d257213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d257213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34987 (p : Pattern) (guard : d257214 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d257213 p = 1 := by simpa only [d257214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34986 p hg
    simpa only [d257214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d257214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34988 (p : Pattern) (guard : d257215 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d257214 p = 1 := by simpa only [d257215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34987 p hg
    simpa only [d257215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d257215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34989 (p : Pattern) (guard : d257216 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d257215 p = 1 := by simpa only [d257216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34988 p hg
    simpa only [d257216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d257216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34990 (p : Pattern) (guard : d257217 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d257217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257216 p = 1 := by simpa only [d257217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34989 p hg
    simpa only [d257217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34991 (p : Pattern) (guard : d257218 p = 1) : d50388 p ≤ (3 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34943 p hg
    simpa only [d257218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257217 p = 1 := by simpa only [d257218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34990 p hg
    simpa only [d257218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34992 (p : Pattern) (guard : d257224 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257224, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34862 p hg
    simpa only [d257224, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257218 p = 1 := by simpa only [d257224, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34991 p hg
    simpa only [d257224, d50389, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34993 (p : Pattern) (guard : d257225 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d257225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d257225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257224 p = 1 := by simpa only [d257225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34992 p hg
    simpa only [d257225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34994 (p : Pattern) (guard : d257226 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d257225 p = 1 := by simpa only [d257226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34993 p hg
    simpa only [d257226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d257226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34995 (p : Pattern) (guard : d257227 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d257226 p = 1 := by simpa only [d257227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34994 p hg
    simpa only [d257227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d257227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34996 (p : Pattern) (guard : d257228 p = 1) : d50389 p ≤ (3 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d257227 p = 1 := by simpa only [d257228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34995 p hg
    simpa only [d257228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d257228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34942 p hg
    simpa only [d257228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34997 (p : Pattern) (guard : d257229 p = 1) : d50390 p ≤ (3 : Int) + d47768 p := by
  cases selected : p 49 with
  | false =>
    have hg : d257223 p = 1 := by simpa only [d257229, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34941 p hg
    simpa only [d257229, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d257228 p = 1 := by simpa only [d257229, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34996 p hg
    simpa only [d257229, d50390, d47768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare34998 (p : Pattern) (guard : d0 p = 1) : d50432 p ≤ (3 : Int) + d47809 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare34999 (p : Pattern) (guard : d0 p = 1) : d50431 p ≤ (3 : Int) + d47808 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Soko22Hazard87
