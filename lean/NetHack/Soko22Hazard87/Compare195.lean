import NetHack.Soko22Hazard87.Compare194
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare48750 (p : Pattern) (guard : d369678 p = 1) : d50642 p ≤ (0 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46055 p = 1 := by simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48746 p hg
    simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369677 p = 1 := by simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48749 p hg
    simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48751 (p : Pattern) (guard : d369679 p = 1) : d50657 p ≤ (0 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369678 p = 1 := by simpa only [d369679, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48750 p hg
    simpa only [d369679, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369679, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d369679, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48752 (p : Pattern) (guard : d369680 p = 1) : d50658 p ≤ (0 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369679 p = 1 := by simpa only [d369680, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48751 p hg
    simpa only [d369680, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369680, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369680, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48753 (p : Pattern) (guard : d369681 p = 1) : d50659 p ≤ (0 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369681, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48127 p hg
    simpa only [d369681, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369680 p = 1 := by simpa only [d369681, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48752 p hg
    simpa only [d369681, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48754 (p : Pattern) (guard : d369682 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369681 p = 1 := by simpa only [d369682, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48753 p hg
    simpa only [d369682, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369682, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48146 p hg
    simpa only [d369682, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48755 (p : Pattern) (guard : d369683 p = 1) : d50642 p ≤ (0 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369502 p = 1 := by simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48523 p hg
    simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369510 p = 1 := by simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48531 p hg
    simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48756 (p : Pattern) (guard : d369684 p = 1) : d50657 p ≤ (0 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369683 p = 1 := by simpa only [d369684, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48755 p hg
    simpa only [d369684, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369684, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d369684, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48757 (p : Pattern) (guard : d369685 p = 1) : d50658 p ≤ (0 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369684 p = 1 := by simpa only [d369685, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48756 p hg
    simpa only [d369685, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369685, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369685, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48758 (p : Pattern) (guard : d369686 p = 1) : d50659 p ≤ (0 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369686, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48127 p hg
    simpa only [d369686, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369685 p = 1 := by simpa only [d369686, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48757 p hg
    simpa only [d369686, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48759 (p : Pattern) (guard : d369687 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369686 p = 1 := by simpa only [d369687, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48758 p hg
    simpa only [d369687, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369687, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48146 p hg
    simpa only [d369687, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48760 (p : Pattern) (guard : d369688 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369682 p = 1 := by simpa only [d369688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48754 p hg
    simpa only [d369688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369687 p = 1 := by simpa only [d369688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48759 p hg
    simpa only [d369688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48761 (p : Pattern) (guard : d369689 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48516 p hg
    simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40692 p hg
    simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48762 (p : Pattern) (guard : d369690 p = 1) : d50642 p ≤ (0 : Int) + d367829 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369689 p = 1 := by simpa only [d369690, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48761 p hg
    simpa only [d369690, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369690, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48138 p hg
    simpa only [d369690, d50642, d367829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48763 (p : Pattern) (guard : d369691 p = 1) : d50642 p ≤ (0 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369690 p = 1 := by simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48762 p hg
    simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369510 p = 1 := by simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48531 p hg
    simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48764 (p : Pattern) (guard : d369692 p = 1) : d50657 p ≤ (0 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369691 p = 1 := by simpa only [d369692, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48763 p hg
    simpa only [d369692, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369692, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d369692, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48765 (p : Pattern) (guard : d369693 p = 1) : d50658 p ≤ (0 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369692 p = 1 := by simpa only [d369693, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48764 p hg
    simpa only [d369693, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369693, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369693, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48766 (p : Pattern) (guard : d369694 p = 1) : d50659 p ≤ (0 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369694, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48127 p hg
    simpa only [d369694, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369693 p = 1 := by simpa only [d369694, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48765 p hg
    simpa only [d369694, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48767 (p : Pattern) (guard : d369695 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369694 p = 1 := by simpa only [d369695, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48766 p hg
    simpa only [d369695, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369695, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48146 p hg
    simpa only [d369695, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48768 (p : Pattern) (guard : d369855 p = 1) : d50642 p ≤ (0 : Int) + d367829 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369389 p = 1 := by simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48326 p hg
    simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48140 p hg
    simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48769 (p : Pattern) (guard : d369856 p = 1) : d50657 p ≤ (0 : Int) + d367846 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369855 p = 1 := by simpa only [d369856, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48768 p hg
    simpa only [d369856, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369856, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d369856, d50657, d367846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48770 (p : Pattern) (guard : d369857 p = 1) : d50658 p ≤ (0 : Int) + d367847 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369856 p = 1 := by simpa only [d369857, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48769 p hg
    simpa only [d369857, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369857, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369857, d50658, d367847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48771 (p : Pattern) (guard : d369858 p = 1) : d50659 p ≤ (0 : Int) + d367863 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369858, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48127 p hg
    simpa only [d369858, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369857 p = 1 := by simpa only [d369858, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48770 p hg
    simpa only [d369858, d50659, d367863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48772 (p : Pattern) (guard : d369859 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369858 p = 1 := by simpa only [d369859, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48771 p hg
    simpa only [d369859, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369859, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48146 p hg
    simpa only [d369859, d50663, d367867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48773 (p : Pattern) (guard : d369860 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369695 p = 1 := by simpa only [d369860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48767 p hg
    simpa only [d369860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369859 p = 1 := by simpa only [d369860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48772 p hg
    simpa only [d369860, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48774 (p : Pattern) (guard : d369861 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369688 p = 1 := by simpa only [d369861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48760 p hg
    simpa only [d369861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369860 p = 1 := by simpa only [d369861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48773 p hg
    simpa only [d369861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48775 (p : Pattern) (guard : d369862 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369507 p = 1 := by simpa only [d369862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48528 p hg
    simpa only [d369862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369859 p = 1 := by simpa only [d369862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48772 p hg
    simpa only [d369862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48776 (p : Pattern) (guard : d369863 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369859 p = 1 := by simpa only [d369863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48772 p hg
    simpa only [d369863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48148 p hg
    simpa only [d369863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48777 (p : Pattern) (guard : d369864 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369862 p = 1 := by simpa only [d369864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48775 p hg
    simpa only [d369864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369863 p = 1 := by simpa only [d369864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48776 p hg
    simpa only [d369864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48778 (p : Pattern) (guard : d369865 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369861 p = 1 := by simpa only [d369865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48774 p hg
    simpa only [d369865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369864 p = 1 := by simpa only [d369865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48777 p hg
    simpa only [d369865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48779 (p : Pattern) (guard : d369866 p = 1) : d50664 p ≤ (0 : Int) + d367868 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369866, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48126 p hg
    simpa only [d369866, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369865 p = 1 := by simpa only [d369866, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48778 p hg
    simpa only [d369866, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48780 (p : Pattern) (guard : d369867 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369867, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48125 p hg
    simpa only [d369867, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369866 p = 1 := by simpa only [d369867, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48779 p hg
    simpa only [d369867, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48781 (p : Pattern) (guard : d369868 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369863 p = 1 := by simpa only [d369868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48776 p hg
    simpa only [d369868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48148 p hg
    simpa only [d369868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48782 (p : Pattern) (guard : d369869 p = 1) : d50663 p ≤ (0 : Int) + d367867 p := by
  cases selected : p 157 with
  | false =>
    have hg : d369864 p = 1 := by simpa only [d369869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48777 p hg
    simpa only [d369869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369868 p = 1 := by simpa only [d369869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48781 p hg
    simpa only [d369869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48783 (p : Pattern) (guard : d369870 p = 1) : d50664 p ≤ (0 : Int) + d367868 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369870, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48126 p hg
    simpa only [d369870, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369869 p = 1 := by simpa only [d369870, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48782 p hg
    simpa only [d369870, d50664, d367868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48784 (p : Pattern) (guard : d369871 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369871, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48125 p hg
    simpa only [d369871, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369870 p = 1 := by simpa only [d369871, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48783 p hg
    simpa only [d369871, d50665, d367869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48785 (p : Pattern) (guard : d369872 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369867 p = 1 := by simpa only [d369872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48780 p hg
    simpa only [d369872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369871 p = 1 := by simpa only [d369872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48784 p hg
    simpa only [d369872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48786 (p : Pattern) (guard : d369873 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 136 with
  | false =>
    have hg : d369871 p = 1 := by simpa only [d369873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48784 p hg
    simpa only [d369873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48154 p hg
    simpa only [d369873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48787 (p : Pattern) (guard : d369874 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369872 p = 1 := by simpa only [d369874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48785 p hg
    simpa only [d369874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369873 p = 1 := by simpa only [d369874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48786 p hg
    simpa only [d369874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48788 (p : Pattern) (guard : d369875 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369874 p = 1 := by simpa only [d369875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48787 p hg
    simpa only [d369875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48154 p hg
    simpa only [d369875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48789 (p : Pattern) (guard : d369876 p = 1) : d50673 p ≤ (0 : Int) + d367877 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369875 p = 1 := by simpa only [d369876, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48788 p hg
    simpa only [d369876, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369876, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48158 p hg
    simpa only [d369876, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48790 (p : Pattern) (guard : d369877 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369877, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48124 p hg
    simpa only [d369877, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369876 p = 1 := by simpa only [d369877, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48789 p hg
    simpa only [d369877, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48791 (p : Pattern) (guard : d369878 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 135 with
  | false =>
    have hg : d369873 p = 1 := by simpa only [d369878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48786 p hg
    simpa only [d369878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48154 p hg
    simpa only [d369878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48792 (p : Pattern) (guard : d369879 p = 1) : d50665 p ≤ (0 : Int) + d367869 p := by
  cases selected : p 119 with
  | false =>
    have hg : d369878 p = 1 := by simpa only [d369879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48791 p hg
    simpa only [d369879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48154 p hg
    simpa only [d369879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48793 (p : Pattern) (guard : d369880 p = 1) : d50673 p ≤ (0 : Int) + d367877 p := by
  cases selected : p 116 with
  | false =>
    have hg : d369879 p = 1 := by simpa only [d369880, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48792 p hg
    simpa only [d369880, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369880, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48158 p hg
    simpa only [d369880, d50673, d367877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48794 (p : Pattern) (guard : d369881 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369881, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48124 p hg
    simpa only [d369881, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369880 p = 1 := by simpa only [d369881, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48793 p hg
    simpa only [d369881, d50674, d367878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48795 (p : Pattern) (guard : d369882 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369877 p = 1 := by simpa only [d369882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48790 p hg
    simpa only [d369882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369881 p = 1 := by simpa only [d369882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48794 p hg
    simpa only [d369882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48796 (p : Pattern) (guard : d369883 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369882 p = 1 := by simpa only [d369883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48795 p hg
    simpa only [d369883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48797 (p : Pattern) (guard : d369884 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369883 p = 1 := by simpa only [d369884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48796 p hg
    simpa only [d369884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48798 (p : Pattern) (guard : d369898 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369884 p = 1 := by simpa only [d369898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48797 p hg
    simpa only [d369898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48799 (p : Pattern) (guard : d369886 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 113 with
  | false =>
    have hg : d369881 p = 1 := by simpa only [d369886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48794 p hg
    simpa only [d369886, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369886, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369886, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48800 (p : Pattern) (guard : d369887 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 96 with
  | false =>
    have hg : d369886 p = 1 := by simpa only [d369887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48799 p hg
    simpa only [d369887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48801 (p : Pattern) (guard : d369888 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 95 with
  | false =>
    have hg : d369887 p = 1 := by simpa only [d369888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48800 p hg
    simpa only [d369888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48802 (p : Pattern) (guard : d369899 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 93 with
  | false =>
    have hg : d369888 p = 1 := by simpa only [d369899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48801 p hg
    simpa only [d369899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48803 (p : Pattern) (guard : d369900 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 91 with
  | false =>
    have hg : d369898 p = 1 := by simpa only [d369900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48798 p hg
    simpa only [d369900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369899 p = 1 := by simpa only [d369900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48802 p hg
    simpa only [d369900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48804 (p : Pattern) (guard : d369901 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369900 p = 1 := by simpa only [d369901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48803 p hg
    simpa only [d369901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48805 (p : Pattern) (guard : d369902 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 89 with
  | false =>
    have hg : d369901 p = 1 := by simpa only [d369902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48804 p hg
    simpa only [d369902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48806 (p : Pattern) (guard : d369903 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369902 p = 1 := by simpa only [d369903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48805 p hg
    simpa only [d369903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48807 (p : Pattern) (guard : d369904 p = 1) : d50674 p ≤ (0 : Int) + d367878 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48123 p hg
    simpa only [d369904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369903 p = 1 := by simpa only [d369904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48806 p hg
    simpa only [d369904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48808 (p : Pattern) (guard : d370525 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370525, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d370525, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369904 p = 1 := by simpa only [d370525, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48807 p hg
    simpa only [d370525, d50675, d367879, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48809 (p : Pattern) (guard : d370526 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d370526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370525 p = 1 := by simpa only [d370526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48808 p hg
    simpa only [d370526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48810 (p : Pattern) (guard : d370527 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 69 with
  | false =>
    have hg : d370526 p = 1 := by simpa only [d370527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48809 p hg
    simpa only [d370527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d370527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48811 (p : Pattern) (guard : d370528 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 51 with
  | false =>
    have hg : d370527 p = 1 := by simpa only [d370528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48810 p hg
    simpa only [d370528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d370528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48812 (p : Pattern) (guard : d370529 p = 1) : d50675 p ≤ (0 : Int) + d367879 p := by
  cases selected : p 50 with
  | false =>
    have hg : d370528 p = 1 := by simpa only [d370529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48811 p hg
    simpa only [d370529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48122 p hg
    simpa only [d370529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48813 (p : Pattern) (guard : d370530 p = 1) : d50676 p ≤ (0 : Int) + d367880 p := by
  cases selected : p 49 with
  | false =>
    have hg : d370524 p = 1 := by simpa only [d370530, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48743 p hg
    simpa only [d370530, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370529 p = 1 := by simpa only [d370530, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48812 p hg
    simpa only [d370530, d50676, d367880, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48814 (p : Pattern) (guard : d46053 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40776 p hg
    simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46043 p = 1 := by simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48579 p hg
    simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48815 (p : Pattern) (guard : d46054 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d46053 p = 1 := by simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48814 p hg
    simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40776 p hg
    simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48816 (p : Pattern) (guard : d46055 p = 1) : d50560 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 182 with
  | false =>
    have hg : d46054 p = 1 := by simpa only [d46055, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48815 p hg
    simpa only [d46055, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46055, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48191 p hg
    simpa only [d46055, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48817 (p : Pattern) (guard : d179205 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40776 p hg
    simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48188 p hg
    simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48818 (p : Pattern) (guard : d369676 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48580 p hg
    simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179205 p = 1 := by simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48817 p hg
    simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48819 (p : Pattern) (guard : d369677 p = 1) : d50560 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369676 p = 1 := by simpa only [d369677, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48818 p hg
    simpa only [d369677, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369677, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48191 p hg
    simpa only [d369677, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48820 (p : Pattern) (guard : d369678 p = 1) : d50560 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46055 p = 1 := by simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48816 p hg
    simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369677 p = 1 := by simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48819 p hg
    simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48821 (p : Pattern) (guard : d369774 p = 1) : d50726 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369774, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48180 p hg
    simpa only [d369774, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369678 p = 1 := by simpa only [d369774, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48820 p hg
    simpa only [d369774, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48822 (p : Pattern) (guard : d369679 p = 1) : d50727 p ≤ (0 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369678 p = 1 := by simpa only [d369679, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48673 p hg
    simpa only [d369679, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369679, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d369679, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48823 (p : Pattern) (guard : d369775 p = 1) : d50728 p ≤ (0 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369774 p = 1 := by simpa only [d369775, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48821 p hg
    simpa only [d369775, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369679 p = 1 := by simpa only [d369775, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48822 p hg
    simpa only [d369775, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48824 (p : Pattern) (guard : d46053 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46043 p = 1 := by simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48596 p hg
    simpa only [d46053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48825 (p : Pattern) (guard : d46054 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d46053 p = 1 := by simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48824 p hg
    simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d46054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48826 (p : Pattern) (guard : d46055 p = 1) : d50562 p ≤ (0 : Int) + d367794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d46054 p = 1 := by simpa only [d46055, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48825 p hg
    simpa only [d46055, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46055, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48208 p hg
    simpa only [d46055, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48827 (p : Pattern) (guard : d179205 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179204 p = 1 := by simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48205 p hg
    simpa only [d179205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48828 (p : Pattern) (guard : d369676 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48597 p hg
    simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179205 p = 1 := by simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48827 p hg
    simpa only [d369676, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48829 (p : Pattern) (guard : d369677 p = 1) : d50562 p ≤ (0 : Int) + d367794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369676 p = 1 := by simpa only [d369677, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48828 p hg
    simpa only [d369677, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369677, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48208 p hg
    simpa only [d369677, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48830 (p : Pattern) (guard : d369678 p = 1) : d50562 p ≤ (0 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d46055 p = 1 := by simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48826 p hg
    simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369677 p = 1 := by simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48829 p hg
    simpa only [d369678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48831 (p : Pattern) (guard : d369679 p = 1) : d50573 p ≤ (0 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369678 p = 1 := by simpa only [d369679, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48830 p hg
    simpa only [d369679, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369679, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369679, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48832 (p : Pattern) (guard : d369680 p = 1) : d50574 p ≤ (0 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369679 p = 1 := by simpa only [d369680, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48831 p hg
    simpa only [d369680, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369680, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369680, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48833 (p : Pattern) (guard : d369776 p = 1) : d50729 p ≤ (0 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d369775 p = 1 := by simpa only [d369776, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48823 p hg
    simpa only [d369776, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369680 p = 1 := by simpa only [d369776, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48832 p hg
    simpa only [d369776, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48834 (p : Pattern) (guard : d369777 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369776 p = 1 := by simpa only [d369777, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48833 p hg
    simpa only [d369777, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369777, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48215 p hg
    simpa only [d369777, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48835 (p : Pattern) (guard : d369683 p = 1) : d50560 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369502 p = 1 := by simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48587 p hg
    simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369510 p = 1 := by simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48612 p hg
    simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48836 (p : Pattern) (guard : d369778 p = 1) : d50726 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369778, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48180 p hg
    simpa only [d369778, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369683 p = 1 := by simpa only [d369778, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48835 p hg
    simpa only [d369778, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48837 (p : Pattern) (guard : d369684 p = 1) : d50727 p ≤ (0 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369683 p = 1 := by simpa only [d369684, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48678 p hg
    simpa only [d369684, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369684, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d369684, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48838 (p : Pattern) (guard : d369779 p = 1) : d50728 p ≤ (0 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369778 p = 1 := by simpa only [d369779, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48836 p hg
    simpa only [d369779, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369684 p = 1 := by simpa only [d369779, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48837 p hg
    simpa only [d369779, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48839 (p : Pattern) (guard : d369683 p = 1) : d50562 p ≤ (0 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369502 p = 1 := by simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48604 p hg
    simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369510 p = 1 := by simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48618 p hg
    simpa only [d369683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48840 (p : Pattern) (guard : d369684 p = 1) : d50573 p ≤ (0 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369683 p = 1 := by simpa only [d369684, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48839 p hg
    simpa only [d369684, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369684, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369684, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48841 (p : Pattern) (guard : d369685 p = 1) : d50574 p ≤ (0 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369684 p = 1 := by simpa only [d369685, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48840 p hg
    simpa only [d369685, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369685, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369685, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48842 (p : Pattern) (guard : d369780 p = 1) : d50729 p ≤ (0 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d369779 p = 1 := by simpa only [d369780, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48838 p hg
    simpa only [d369780, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369685 p = 1 := by simpa only [d369780, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48841 p hg
    simpa only [d369780, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48843 (p : Pattern) (guard : d369781 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369780 p = 1 := by simpa only [d369781, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48842 p hg
    simpa only [d369781, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369781, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48215 p hg
    simpa only [d369781, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48844 (p : Pattern) (guard : d369782 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369777 p = 1 := by simpa only [d369782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48834 p hg
    simpa only [d369782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369781 p = 1 := by simpa only [d369782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48843 p hg
    simpa only [d369782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48845 (p : Pattern) (guard : d369689 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48580 p hg
    simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40776 p hg
    simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48846 (p : Pattern) (guard : d369690 p = 1) : d50560 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369689 p = 1 := by simpa only [d369690, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48845 p hg
    simpa only [d369690, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369690, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48191 p hg
    simpa only [d369690, d50560, d367780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48847 (p : Pattern) (guard : d369691 p = 1) : d50560 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369690 p = 1 := by simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48846 p hg
    simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369510 p = 1 := by simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48612 p hg
    simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48848 (p : Pattern) (guard : d369783 p = 1) : d50726 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d369783, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48180 p hg
    simpa only [d369783, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369691 p = 1 := by simpa only [d369783, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48847 p hg
    simpa only [d369783, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48849 (p : Pattern) (guard : d369692 p = 1) : d50727 p ≤ (0 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369691 p = 1 := by simpa only [d369692, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48686 p hg
    simpa only [d369692, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369692, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d369692, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48850 (p : Pattern) (guard : d369784 p = 1) : d50728 p ≤ (0 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369783 p = 1 := by simpa only [d369784, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48848 p hg
    simpa only [d369784, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369692 p = 1 := by simpa only [d369784, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48849 p hg
    simpa only [d369784, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48851 (p : Pattern) (guard : d369689 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d369497 p = 1 := by simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48597 p hg
    simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d369689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48852 (p : Pattern) (guard : d369690 p = 1) : d50562 p ≤ (0 : Int) + d367794 p := by
  cases selected : p 182 with
  | false =>
    have hg : d369689 p = 1 := by simpa only [d369690, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48851 p hg
    simpa only [d369690, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369690, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48208 p hg
    simpa only [d369690, d50562, d367794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48853 (p : Pattern) (guard : d369691 p = 1) : d50562 p ≤ (0 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369690 p = 1 := by simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48852 p hg
    simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369510 p = 1 := by simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48618 p hg
    simpa only [d369691, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48854 (p : Pattern) (guard : d369692 p = 1) : d50573 p ≤ (0 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369691 p = 1 := by simpa only [d369692, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48853 p hg
    simpa only [d369692, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369692, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369692, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48855 (p : Pattern) (guard : d369693 p = 1) : d50574 p ≤ (0 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369692 p = 1 := by simpa only [d369693, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48854 p hg
    simpa only [d369693, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369693, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369693, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48856 (p : Pattern) (guard : d369785 p = 1) : d50729 p ≤ (0 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d369784 p = 1 := by simpa only [d369785, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48850 p hg
    simpa only [d369785, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369693 p = 1 := by simpa only [d369785, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48855 p hg
    simpa only [d369785, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48857 (p : Pattern) (guard : d369786 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d369785 p = 1 := by simpa only [d369786, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48856 p hg
    simpa only [d369786, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369786, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48215 p hg
    simpa only [d369786, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48858 (p : Pattern) (guard : d369855 p = 1) : d50560 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369389 p = 1 := by simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48375 p hg
    simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48193 p hg
    simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48859 (p : Pattern) (guard : d370026 p = 1) : d50726 p ≤ (0 : Int) + d367780 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370026, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48180 p hg
    simpa only [d370026, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369855 p = 1 := by simpa only [d370026, d50726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48858 p hg
    simpa only [d370026, d50726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48860 (p : Pattern) (guard : d369856 p = 1) : d50727 p ≤ (0 : Int) + d367911 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369855 p = 1 := by simpa only [d369856, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48691 p hg
    simpa only [d369856, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369856, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48142 p hg
    simpa only [d369856, d50727, d367911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48861 (p : Pattern) (guard : d370027 p = 1) : d50728 p ≤ (0 : Int) + d367912 p := by
  cases selected : p 162 with
  | false =>
    have hg : d370026 p = 1 := by simpa only [d370027, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48859 p hg
    simpa only [d370027, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369856 p = 1 := by simpa only [d370027, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48860 p hg
    simpa only [d370027, d50728, d367912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48862 (p : Pattern) (guard : d369855 p = 1) : d50562 p ≤ (0 : Int) + d367794 p := by
  cases selected : p 180 with
  | false =>
    have hg : d369389 p = 1 := by simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48397 p hg
    simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48210 p hg
    simpa only [d369855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48863 (p : Pattern) (guard : d369856 p = 1) : d50573 p ≤ (0 : Int) + d367802 p := by
  cases selected : p 163 with
  | false =>
    have hg : d369855 p = 1 := by simpa only [d369856, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48862 p hg
    simpa only [d369856, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369856, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369856, d50573, d367802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48864 (p : Pattern) (guard : d369857 p = 1) : d50574 p ≤ (0 : Int) + d367803 p := by
  cases selected : p 162 with
  | false =>
    have hg : d369856 p = 1 := by simpa only [d369857, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48863 p hg
    simpa only [d369857, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d369857, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d369857, d50574, d367803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48865 (p : Pattern) (guard : d370028 p = 1) : d50729 p ≤ (0 : Int) + d367913 p := by
  cases selected : p 161 with
  | false =>
    have hg : d370027 p = 1 := by simpa only [d370028, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48861 p hg
    simpa only [d370028, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d369857 p = 1 := by simpa only [d370028, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48864 p hg
    simpa only [d370028, d50729, d367913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48866 (p : Pattern) (guard : d370029 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 160 with
  | false =>
    have hg : d370028 p = 1 := by simpa only [d370029, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48865 p hg
    simpa only [d370029, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370029, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48215 p hg
    simpa only [d370029, d50733, d367917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48867 (p : Pattern) (guard : d370030 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369786 p = 1 := by simpa only [d370030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48857 p hg
    simpa only [d370030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370029 p = 1 := by simpa only [d370030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48866 p hg
    simpa only [d370030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48868 (p : Pattern) (guard : d370031 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 158 with
  | false =>
    have hg : d369782 p = 1 := by simpa only [d370031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48844 p hg
    simpa only [d370031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370030 p = 1 := by simpa only [d370031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48867 p hg
    simpa only [d370031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48869 (p : Pattern) (guard : d370041 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d369578 p = 1 := by simpa only [d370041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48609 p hg
    simpa only [d370041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370029 p = 1 := by simpa only [d370041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48866 p hg
    simpa only [d370041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48870 (p : Pattern) (guard : d370035 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 159 with
  | false =>
    have hg : d370029 p = 1 := by simpa only [d370035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48866 p hg
    simpa only [d370035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48217 p hg
    simpa only [d370035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48871 (p : Pattern) (guard : d370042 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 158 with
  | false =>
    have hg : d370041 p = 1 := by simpa only [d370042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48869 p hg
    simpa only [d370042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370035 p = 1 := by simpa only [d370042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48870 p hg
    simpa only [d370042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48872 (p : Pattern) (guard : d370043 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 157 with
  | false =>
    have hg : d370031 p = 1 := by simpa only [d370043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48868 p hg
    simpa only [d370043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370042 p = 1 := by simpa only [d370043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48871 p hg
    simpa only [d370043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48873 (p : Pattern) (guard : d370044 p = 1) : d50734 p ≤ (0 : Int) + d367918 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370044, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48179 p hg
    simpa only [d370044, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370043 p = 1 := by simpa only [d370044, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48872 p hg
    simpa only [d370044, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48874 (p : Pattern) (guard : d370045 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370045, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48178 p hg
    simpa only [d370045, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370044 p = 1 := by simpa only [d370045, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48873 p hg
    simpa only [d370045, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48875 (p : Pattern) (guard : d370046 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 158 with
  | false =>
    have hg : d370035 p = 1 := by simpa only [d370046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48870 p hg
    simpa only [d370046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48217 p hg
    simpa only [d370046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48876 (p : Pattern) (guard : d370047 p = 1) : d50733 p ≤ (0 : Int) + d367917 p := by
  cases selected : p 157 with
  | false =>
    have hg : d370042 p = 1 := by simpa only [d370047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48871 p hg
    simpa only [d370047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370046 p = 1 := by simpa only [d370047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48875 p hg
    simpa only [d370047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48877 (p : Pattern) (guard : d370048 p = 1) : d50734 p ≤ (0 : Int) + d367918 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370048, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48179 p hg
    simpa only [d370048, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370047 p = 1 := by simpa only [d370048, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48876 p hg
    simpa only [d370048, d50734, d367918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48878 (p : Pattern) (guard : d370049 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370049, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48178 p hg
    simpa only [d370049, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370048 p = 1 := by simpa only [d370049, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48877 p hg
    simpa only [d370049, d50735, d367919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48879 (p : Pattern) (guard : d370050 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 136 with
  | false =>
    have hg : d370045 p = 1 := by simpa only [d370050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48874 p hg
    simpa only [d370050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370049 p = 1 := by simpa only [d370050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48878 p hg
    simpa only [d370050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48880 (p : Pattern) (guard : d370055 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 136 with
  | false =>
    have hg : d370049 p = 1 := by simpa only [d370055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48878 p hg
    simpa only [d370055, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370055, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48223 p hg
    simpa only [d370055, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48881 (p : Pattern) (guard : d370056 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 135 with
  | false =>
    have hg : d370050 p = 1 := by simpa only [d370056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48879 p hg
    simpa only [d370056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370055 p = 1 := by simpa only [d370056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48880 p hg
    simpa only [d370056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48882 (p : Pattern) (guard : d370057 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 119 with
  | false =>
    have hg : d370056 p = 1 := by simpa only [d370057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48881 p hg
    simpa only [d370057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48223 p hg
    simpa only [d370057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48883 (p : Pattern) (guard : d370058 p = 1) : d50737 p ≤ (0 : Int) + d367921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d370057 p = 1 := by simpa only [d370058, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48882 p hg
    simpa only [d370058, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370058, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48227 p hg
    simpa only [d370058, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48884 (p : Pattern) (guard : d370059 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370059, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48063 p hg
    simpa only [d370059, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370058 p = 1 := by simpa only [d370059, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48883 p hg
    simpa only [d370059, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48885 (p : Pattern) (guard : d370064 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 135 with
  | false =>
    have hg : d370055 p = 1 := by simpa only [d370064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48880 p hg
    simpa only [d370064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48223 p hg
    simpa only [d370064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48886 (p : Pattern) (guard : d370065 p = 1) : d50735 p ≤ (0 : Int) + d367919 p := by
  cases selected : p 119 with
  | false =>
    have hg : d370064 p = 1 := by simpa only [d370065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48885 p hg
    simpa only [d370065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48223 p hg
    simpa only [d370065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48887 (p : Pattern) (guard : d370066 p = 1) : d50737 p ≤ (0 : Int) + d367921 p := by
  cases selected : p 116 with
  | false =>
    have hg : d370065 p = 1 := by simpa only [d370066, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48886 p hg
    simpa only [d370066, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370066, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48227 p hg
    simpa only [d370066, d50737, d367921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48888 (p : Pattern) (guard : d370067 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370067, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48063 p hg
    simpa only [d370067, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370066 p = 1 := by simpa only [d370067, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48887 p hg
    simpa only [d370067, d50738, d367922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48889 (p : Pattern) (guard : d370068 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d370059 p = 1 := by simpa only [d370068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48884 p hg
    simpa only [d370068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370067 p = 1 := by simpa only [d370068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48888 p hg
    simpa only [d370068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48890 (p : Pattern) (guard : d370069 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d370068 p = 1 := by simpa only [d370069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48889 p hg
    simpa only [d370069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48891 (p : Pattern) (guard : d370070 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d370069 p = 1 := by simpa only [d370070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48890 p hg
    simpa only [d370070, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370070, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370070, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48892 (p : Pattern) (guard : d370071 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d370070 p = 1 := by simpa only [d370071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48891 p hg
    simpa only [d370071, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370071, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370071, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48893 (p : Pattern) (guard : d370085 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 113 with
  | false =>
    have hg : d370067 p = 1 := by simpa only [d370085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48888 p hg
    simpa only [d370085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48894 (p : Pattern) (guard : d370086 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 96 with
  | false =>
    have hg : d370085 p = 1 := by simpa only [d370086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48893 p hg
    simpa only [d370086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48895 (p : Pattern) (guard : d370087 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 95 with
  | false =>
    have hg : d370086 p = 1 := by simpa only [d370087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48894 p hg
    simpa only [d370087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48896 (p : Pattern) (guard : d370088 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 93 with
  | false =>
    have hg : d370087 p = 1 := by simpa only [d370088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48895 p hg
    simpa only [d370088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48897 (p : Pattern) (guard : d370531 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 91 with
  | false =>
    have hg : d370071 p = 1 := by simpa only [d370531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48892 p hg
    simpa only [d370531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370088 p = 1 := by simpa only [d370531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48896 p hg
    simpa only [d370531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48898 (p : Pattern) (guard : d370532 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370531 p = 1 := by simpa only [d370532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48897 p hg
    simpa only [d370532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48899 (p : Pattern) (guard : d370533 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 89 with
  | false =>
    have hg : d370532 p = 1 := by simpa only [d370533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48898 p hg
    simpa only [d370533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48900 (p : Pattern) (guard : d370534 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370533 p = 1 := by simpa only [d370534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48899 p hg
    simpa only [d370534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48901 (p : Pattern) (guard : d370535 p = 1) : d50738 p ≤ (0 : Int) + d367922 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48177 p hg
    simpa only [d370535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370534 p = 1 := by simpa only [d370535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48900 p hg
    simpa only [d370535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48902 (p : Pattern) (guard : d370536 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370536, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48062 p hg
    simpa only [d370536, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370535 p = 1 := by simpa only [d370536, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48901 p hg
    simpa only [d370536, d50739, d367923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48903 (p : Pattern) (guard : d370537 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d370537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370536 p = 1 := by simpa only [d370537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48902 p hg
    simpa only [d370537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48904 (p : Pattern) (guard : d370538 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 69 with
  | false =>
    have hg : d370537 p = 1 := by simpa only [d370538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48903 p hg
    simpa only [d370538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d370538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48905 (p : Pattern) (guard : d370539 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 51 with
  | false =>
    have hg : d370538 p = 1 := by simpa only [d370539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48904 p hg
    simpa only [d370539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d370539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48906 (p : Pattern) (guard : d370540 p = 1) : d50739 p ≤ (0 : Int) + d367923 p := by
  cases selected : p 50 with
  | false =>
    have hg : d370539 p = 1 := by simpa only [d370540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48905 p hg
    simpa only [d370540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48176 p hg
    simpa only [d370540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48907 (p : Pattern) (guard : d370541 p = 1) : d50822 p ≤ (0 : Int) + d367984 p := by
  cases selected : p 49 with
  | false =>
    have hg : d370540 p = 1 := by simpa only [d370541, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48906 p hg
    simpa only [d370541, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370541, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48244 p hg
    simpa only [d370541, d50822, d367984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48908 (p : Pattern) (guard : d370542 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 48 with
  | false =>
    have hg : d370530 p = 1 := by simpa only [d370542, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48813 p hg
    simpa only [d370542, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370541 p = 1 := by simpa only [d370542, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48907 p hg
    simpa only [d370542, d50823, d367985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48909 (p : Pattern) (guard : d370543 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370542 p = 1 := by simpa only [d370543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48908 p hg
    simpa only [d370543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48910 (p : Pattern) (guard : d370544 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370543 p = 1 := by simpa only [d370544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48909 p hg
    simpa only [d370544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48911 (p : Pattern) (guard : d370545 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370544 p = 1 := by simpa only [d370545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48910 p hg
    simpa only [d370545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48912 (p : Pattern) (guard : d370546 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370545 p = 1 := by simpa only [d370546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48911 p hg
    simpa only [d370546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48913 (p : Pattern) (guard : d370547 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370546 p = 1 := by simpa only [d370547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48912 p hg
    simpa only [d370547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48914 (p : Pattern) (guard : d370548 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370547 p = 1 := by simpa only [d370548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48913 p hg
    simpa only [d370548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48915 (p : Pattern) (guard : d370549 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370548 p = 1 := by simpa only [d370549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48914 p hg
    simpa only [d370549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48916 (p : Pattern) (guard : d370550 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d370550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370549 p = 1 := by simpa only [d370550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48915 p hg
    simpa only [d370550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48917 (p : Pattern) (guard : d370551 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d370522 p = 1 := by simpa only [d370551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48666 p hg
    simpa only [d370551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d370550 p = 1 := by simpa only [d370551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48916 p hg
    simpa only [d370551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48918 (p : Pattern) (guard : d370626 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d370551 p = 1 := by simpa only [d370626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48917 p hg
    simpa only [d370626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48919 (p : Pattern) (guard : d370627 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d370626 p = 1 := by simpa only [d370627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48918 p hg
    simpa only [d370627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48920 (p : Pattern) (guard : d370628 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 260 with
  | false =>
    have hg : d370627 p = 1 := by simpa only [d370628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48919 p hg
    simpa only [d370628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48921 (p : Pattern) (guard : d370629 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 259 with
  | false =>
    have hg : d370628 p = 1 := by simpa only [d370629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48920 p hg
    simpa only [d370629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48922 (p : Pattern) (guard : d370630 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 258 with
  | false =>
    have hg : d370629 p = 1 := by simpa only [d370630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48921 p hg
    simpa only [d370630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48923 (p : Pattern) (guard : d370631 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 257 with
  | false =>
    have hg : d370630 p = 1 := by simpa only [d370631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48922 p hg
    simpa only [d370631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48924 (p : Pattern) (guard : d370632 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 256 with
  | false =>
    have hg : d370631 p = 1 := by simpa only [d370632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48923 p hg
    simpa only [d370632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48925 (p : Pattern) (guard : d370633 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 255 with
  | false =>
    have hg : d370632 p = 1 := by simpa only [d370633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48924 p hg
    simpa only [d370633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48926 (p : Pattern) (guard : d370634 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 254 with
  | false =>
    have hg : d370633 p = 1 := by simpa only [d370634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48925 p hg
    simpa only [d370634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48927 (p : Pattern) (guard : d370635 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 253 with
  | false =>
    have hg : d370634 p = 1 := by simpa only [d370635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48926 p hg
    simpa only [d370635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48928 (p : Pattern) (guard : d370636 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 252 with
  | false =>
    have hg : d370635 p = 1 := by simpa only [d370636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48927 p hg
    simpa only [d370636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48929 (p : Pattern) (guard : d370637 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 251 with
  | false =>
    have hg : d370636 p = 1 := by simpa only [d370637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48928 p hg
    simpa only [d370637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48930 (p : Pattern) (guard : d370638 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 250 with
  | false =>
    have hg : d370637 p = 1 := by simpa only [d370638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48929 p hg
    simpa only [d370638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48931 (p : Pattern) (guard : d370639 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 249 with
  | false =>
    have hg : d370638 p = 1 := by simpa only [d370639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48930 p hg
    simpa only [d370639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48932 (p : Pattern) (guard : d370640 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 245 with
  | false =>
    have hg : d370639 p = 1 := by simpa only [d370640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48931 p hg
    simpa only [d370640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48933 (p : Pattern) (guard : d370641 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 200 with
  | false =>
    have hg : d370640 p = 1 := by simpa only [d370641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48932 p hg
    simpa only [d370641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48934 (p : Pattern) (guard : d370642 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 199 with
  | false =>
    have hg : d370641 p = 1 := by simpa only [d370642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48933 p hg
    simpa only [d370642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48935 (p : Pattern) (guard : d370643 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 186 with
  | false =>
    have hg : d370642 p = 1 := by simpa only [d370643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48934 p hg
    simpa only [d370643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48936 (p : Pattern) (guard : d370644 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 185 with
  | false =>
    have hg : d370643 p = 1 := by simpa only [d370644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48935 p hg
    simpa only [d370644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48937 (p : Pattern) (guard : d370645 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 184 with
  | false =>
    have hg : d370644 p = 1 := by simpa only [d370645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48936 p hg
    simpa only [d370645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48938 (p : Pattern) (guard : d370646 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 181 with
  | false =>
    have hg : d370645 p = 1 := by simpa only [d370646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48937 p hg
    simpa only [d370646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48939 (p : Pattern) (guard : d370647 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 177 with
  | false =>
    have hg : d370646 p = 1 := by simpa only [d370647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48938 p hg
    simpa only [d370647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48940 (p : Pattern) (guard : d370648 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 164 with
  | false =>
    have hg : d370647 p = 1 := by simpa only [d370648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48939 p hg
    simpa only [d370648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48941 (p : Pattern) (guard : d370649 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 156 with
  | false =>
    have hg : d370648 p = 1 := by simpa only [d370649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48940 p hg
    simpa only [d370649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48942 (p : Pattern) (guard : d370650 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 155 with
  | false =>
    have hg : d370649 p = 1 := by simpa only [d370650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48941 p hg
    simpa only [d370650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48943 (p : Pattern) (guard : d370651 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 134 with
  | false =>
    have hg : d370650 p = 1 := by simpa only [d370651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48942 p hg
    simpa only [d370651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48944 (p : Pattern) (guard : d370652 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 133 with
  | false =>
    have hg : d370651 p = 1 := by simpa only [d370652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48943 p hg
    simpa only [d370652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48945 (p : Pattern) (guard : d370653 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 120 with
  | false =>
    have hg : d370652 p = 1 := by simpa only [d370653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48944 p hg
    simpa only [d370653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48946 (p : Pattern) (guard : d370654 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 118 with
  | false =>
    have hg : d370653 p = 1 := by simpa only [d370654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48945 p hg
    simpa only [d370654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48947 (p : Pattern) (guard : d370655 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 114 with
  | false =>
    have hg : d370654 p = 1 := by simpa only [d370655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48946 p hg
    simpa only [d370655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48948 (p : Pattern) (guard : d370656 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 111 with
  | false =>
    have hg : d370655 p = 1 := by simpa only [d370656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48947 p hg
    simpa only [d370656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48949 (p : Pattern) (guard : d370657 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 98 with
  | false =>
    have hg : d370656 p = 1 := by simpa only [d370657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48948 p hg
    simpa only [d370657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48950 (p : Pattern) (guard : d370658 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 97 with
  | false =>
    have hg : d370657 p = 1 := by simpa only [d370658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48949 p hg
    simpa only [d370658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48951 (p : Pattern) (guard : d370659 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 94 with
  | false =>
    have hg : d370658 p = 1 := by simpa only [d370659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48950 p hg
    simpa only [d370659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48952 (p : Pattern) (guard : d370660 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 76 with
  | false =>
    have hg : d370659 p = 1 := by simpa only [d370660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48951 p hg
    simpa only [d370660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48953 (p : Pattern) (guard : d370661 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 67 with
  | false =>
    have hg : d370660 p = 1 := by simpa only [d370661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48952 p hg
    simpa only [d370661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48954 (p : Pattern) (guard : d370662 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 52 with
  | false =>
    have hg : d370661 p = 1 := by simpa only [d370662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48953 p hg
    simpa only [d370662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48955 (p : Pattern) (guard : d370663 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 47 with
  | false =>
    have hg : d370662 p = 1 := by simpa only [d370663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48954 p hg
    simpa only [d370663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48956 (p : Pattern) (guard : d370664 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 46 with
  | false =>
    have hg : d370663 p = 1 := by simpa only [d370664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48955 p hg
    simpa only [d370664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48957 (p : Pattern) (guard : d370665 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 45 with
  | false =>
    have hg : d370664 p = 1 := by simpa only [d370665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48956 p hg
    simpa only [d370665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48958 (p : Pattern) (guard : d370666 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 30 with
  | false =>
    have hg : d370665 p = 1 := by simpa only [d370666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48957 p hg
    simpa only [d370666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48959 (p : Pattern) (guard : d370667 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 29 with
  | false =>
    have hg : d370666 p = 1 := by simpa only [d370667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48958 p hg
    simpa only [d370667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48960 (p : Pattern) (guard : d370668 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 28 with
  | false =>
    have hg : d370667 p = 1 := by simpa only [d370668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48959 p hg
    simpa only [d370668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48961 (p : Pattern) (guard : d370669 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 27 with
  | false =>
    have hg : d370668 p = 1 := by simpa only [d370669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48960 p hg
    simpa only [d370669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48962 (p : Pattern) (guard : d370670 p = 1) : d50823 p ≤ (0 : Int) + d367985 p := by
  cases selected : p 25 with
  | false =>
    have hg : d370669 p = 1 := by simpa only [d370670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48961 p hg
    simpa only [d370670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d370670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48061 p hg
    simpa only [d370670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48963 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (1 : Int) + d371353 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48964 (p : Pattern) (guard : d0 p = 1) : d50591 p ≤ (1 : Int) + d371079 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48965 (p : Pattern) (guard : d0 p = 1) : d50588 p ≤ (1 : Int) + d371076 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48966 (p : Pattern) (guard : d0 p = 1) : d50546 p ≤ (1 : Int) + d371028 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48967 (p : Pattern) (guard : d0 p = 1) : d50566 p ≤ (1 : Int) + d371054 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48968 (p : Pattern) (guard : d0 p = 1) : d50576 p ≤ (1 : Int) + d371064 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48969 (p : Pattern) (guard : d0 p = 1) : d50569 p ≤ (1 : Int) + d371057 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48970 (p : Pattern) (guard : d0 p = 1) : d50553 p ≤ (1 : Int) + d371040 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48971 (p : Pattern) (guard : d0 p = 1) : d47617 p ≤ (1 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48972 (p : Pattern) (guard : d0 p = 1) : d49396 p ≤ (1 : Int) + d370984 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48973 (p : Pattern) (guard : d44880 p = 1) : d4 p ≤ (1 : Int) + d4 p := by
  omega
theorem compare48974 (p : Pattern) (guard : d0 p = 1) : d47616 p ≤ (1 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48975 (p : Pattern) (guard : d46864 p = 1) : d47617 p ≤ (1 : Int) + d4 p := by
  cases selected : p 246 with
  | false =>
    have hg : d44880 p = 1 := by simpa only [d46864, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48973 p hg
    simpa only [d46864, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46864, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48974 p hg
    simpa only [d46864, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48976 (p : Pattern) (guard : d46865 p = 1) : d47617 p ≤ (1 : Int) + d4 p := by
  cases selected : p 226 with
  | false =>
    have hg : d46864 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48975 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48971 p hg
    simpa only [d46865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48977 (p : Pattern) (guard : d0 p = 1) : d49391 p ≤ (1 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48978 (p : Pattern) (guard : d46866 p = 1) : d49392 p ≤ (1 : Int) + d370982 p := by
  cases selected : p 225 with
  | false =>
    have hg : d46865 p = 1 := by simpa only [d46866, d49392, d370982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48976 p hg
    simpa only [d46866, d49392, d370982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46866, d49392, d370982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48977 p hg
    simpa only [d46866, d49392, d370982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48979 (p : Pattern) (guard : d0 p = 1) : d49395 p ≤ (1 : Int) + d370983 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48980 (p : Pattern) (guard : d46867 p = 1) : d49396 p ≤ (1 : Int) + d370984 p := by
  cases selected : p 224 with
  | false =>
    have hg : d46866 p = 1 := by simpa only [d46867, d49396, d370984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48978 p hg
    simpa only [d46867, d49396, d370984, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46867, d49396, d370984, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48979 p hg
    simpa only [d46867, d49396, d370984, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48981 (p : Pattern) (guard : d46868 p = 1) : d49396 p ≤ (1 : Int) + d370984 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48972 p hg
    simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46867 p = 1 := by simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48980 p hg
    simpa only [d46868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48982 (p : Pattern) (guard : d46869 p = 1) : d50510 p ≤ (1 : Int) + d370985 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46869, d50510, d370985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48971 p hg
    simpa only [d46869, d50510, d370985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46868 p = 1 := by simpa only [d46869, d50510, d370985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48981 p hg
    simpa only [d46869, d50510, d370985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48983 (p : Pattern) (guard : d0 p = 1) : d50510 p ≤ (1 : Int) + d370985 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48984 (p : Pattern) (guard : d46870 p = 1) : d50510 p ≤ (1 : Int) + d370985 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46869 p = 1 := by simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48982 p hg
    simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48983 p hg
    simpa only [d46870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48985 (p : Pattern) (guard : d46871 p = 1) : d49396 p ≤ (1 : Int) + d370984 p := by
  cases selected : p 223 with
  | false =>
    have hg : d46867 p = 1 := by simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48980 p hg
    simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48972 p hg
    simpa only [d46871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48986 (p : Pattern) (guard : d46872 p = 1) : d50510 p ≤ (1 : Int) + d370985 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46872, d50510, d370985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48971 p hg
    simpa only [d46872, d50510, d370985, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46871 p = 1 := by simpa only [d46872, d50510, d370985, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48985 p hg
    simpa only [d46872, d50510, d370985, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48987 (p : Pattern) (guard : d46873 p = 1) : d50510 p ≤ (1 : Int) + d370985 p := by
  cases selected : p 202 with
  | false =>
    have hg : d46872 p = 1 := by simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48986 p hg
    simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48983 p hg
    simpa only [d46873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48988 (p : Pattern) (guard : d46874 p = 1) : d50510 p ≤ (1 : Int) + d370985 p := by
  cases selected : p 201 with
  | false =>
    have hg : d46870 p = 1 := by simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48984 p hg
    simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46873 p = 1 := by simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48987 p hg
    simpa only [d46874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48989 (p : Pattern) (guard : d0 p = 1) : d49397 p ≤ (1 : Int) + d371039 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48990 (p : Pattern) (guard : d46875 p = 1) : d50553 p ≤ (1 : Int) + d371040 p := by
  cases selected : p 182 with
  | false =>
    have hg : d46874 p = 1 := by simpa only [d46875, d50553, d371040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48988 p hg
    simpa only [d46875, d50553, d371040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46875, d50553, d371040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48989 p hg
    simpa only [d46875, d50553, d371040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48991 (p : Pattern) (guard : d46876 p = 1) : d50553 p ≤ (1 : Int) + d371040 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48970 p hg
    simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46875 p = 1 := by simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48990 p hg
    simpa only [d46876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48992 (p : Pattern) (guard : d0 p = 1) : d50527 p ≤ (1 : Int) + d371009 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48993 (p : Pattern) (guard : d46877 p = 1) : d50570 p ≤ (1 : Int) + d371058 p := by
  cases selected : p 163 with
  | false =>
    have hg : d46876 p = 1 := by simpa only [d46877, d50570, d371058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48991 p hg
    simpa only [d46877, d50570, d371058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46877, d50570, d371058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48992 p hg
    simpa only [d46877, d50570, d371058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48994 (p : Pattern) (guard : d0 p = 1) : d50531 p ≤ (1 : Int) + d371013 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48995 (p : Pattern) (guard : d46878 p = 1) : d50571 p ≤ (1 : Int) + d371059 p := by
  cases selected : p 162 with
  | false =>
    have hg : d46877 p = 1 := by simpa only [d46878, d50571, d371059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48993 p hg
    simpa only [d46878, d50571, d371059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46878, d50571, d371059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48994 p hg
    simpa only [d46878, d50571, d371059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48996 (p : Pattern) (guard : d46879 p = 1) : d50572 p ≤ (1 : Int) + d371060 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46879, d50572, d371060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48969 p hg
    simpa only [d46879, d50572, d371060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46878 p = 1 := by simpa only [d46879, d50572, d371060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48995 p hg
    simpa only [d46879, d50572, d371060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48997 (p : Pattern) (guard : d0 p = 1) : d50575 p ≤ (1 : Int) + d371063 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare48998 (p : Pattern) (guard : d46880 p = 1) : d50576 p ≤ (1 : Int) + d371064 p := by
  cases selected : p 160 with
  | false =>
    have hg : d46879 p = 1 := by simpa only [d46880, d50576, d371064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48996 p hg
    simpa only [d46880, d50576, d371064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d46880, d50576, d371064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48997 p hg
    simpa only [d46880, d50576, d371064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48999 (p : Pattern) (guard : d46881 p = 1) : d50576 p ≤ (1 : Int) + d371064 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48968 p hg
    simpa only [d46881, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46880 p = 1 := by simpa only [d46881, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48998 p hg
    simpa only [d46881, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
