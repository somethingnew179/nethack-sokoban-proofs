import NetHack.Soko22Hazard87.Compare103
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare26000 (p : Pattern) (guard : d16273 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14530 p = 1 := by simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25999 p hg
    simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12749 p = 1 := by simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25814 p hg
    simpa only [d16273, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26001 (p : Pattern) (guard : d16274 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16272 p = 1 := by simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25991 p hg
    simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16273 p = 1 := by simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26000 p hg
    simpa only [d16274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26002 (p : Pattern) (guard : d750 p = 1) : d47615 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25586 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25510 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26003 (p : Pattern) (guard : d751 p = 1) : d47653 p ≤ (-1 : Int) + d47652 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26002 p hg
    simpa only [d751, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25512 p hg
    simpa only [d751, d47653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26004 (p : Pattern) (guard : d752 p = 1) : d48565 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 162 with
  | false =>
    have hg : d751 p = 1 := by simpa only [d752, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26003 p hg
    simpa only [d752, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d752, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25514 p hg
    simpa only [d752, d48565, d48498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26005 (p : Pattern) (guard : d753 p = 1) : d48601 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25496 p hg
    simpa only [d753, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d48601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26004 p hg
    simpa only [d753, d48601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26006 (p : Pattern) (guard : d754 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26005 p hg
    simpa only [d754, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d48602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25517 p hg
    simpa only [d754, d48602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26007 (p : Pattern) (guard : d12750 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d12749 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25814 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26006 p hg
    simpa only [d12750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26008 (p : Pattern) (guard : d16227 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16075 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25806 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d12750 p = 1 := by simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26007 p hg
    simpa only [d16227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26009 (p : Pattern) (guard : d16275 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16274 p = 1 := by simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26001 p hg
    simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16227 p = 1 := by simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26008 p hg
    simpa only [d16275, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26010 (p : Pattern) (guard : d18868 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16275 p = 1 := by simpa only [d18868, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26009 p hg
    simpa only [d18868, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18868, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d18868, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26011 (p : Pattern) (guard : d18869 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d18869, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d18869, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18868 p = 1 := by simpa only [d18869, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26010 p hg
    simpa only [d18869, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26012 (p : Pattern) (guard : d757 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26006 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26013 (p : Pattern) (guard : d16278 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d12750 p = 1 := by simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26007 p hg
    simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26012 p hg
    simpa only [d16278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26014 (p : Pattern) (guard : d16279 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26008 p hg
    simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16278 p = 1 := by simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26013 p hg
    simpa only [d16279, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26015 (p : Pattern) (guard : d18870 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16279 p = 1 := by simpa only [d18870, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26014 p hg
    simpa only [d18870, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18870, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d18870, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26016 (p : Pattern) (guard : d18871 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d18871, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d18871, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18870 p = 1 := by simpa only [d18871, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26015 p hg
    simpa only [d18871, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26017 (p : Pattern) (guard : d18872 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d18869 p = 1 := by simpa only [d18872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26011 p hg
    simpa only [d18872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18871 p = 1 := by simpa only [d18872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26016 p hg
    simpa only [d18872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26018 (p : Pattern) (guard : d755 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25671 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26006 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26019 (p : Pattern) (guard : d758 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26018 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26012 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26020 (p : Pattern) (guard : d16228 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16227 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26008 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26019 p hg
    simpa only [d16228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26021 (p : Pattern) (guard : d18873 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d16228 p = 1 := by simpa only [d18873, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26020 p hg
    simpa only [d18873, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18873, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d18873, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26022 (p : Pattern) (guard : d18874 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d18874, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d18874, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18873 p = 1 := by simpa only [d18874, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26021 p hg
    simpa only [d18874, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26023 (p : Pattern) (guard : d762 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26012 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26024 (p : Pattern) (guard : d763 p = 1) : d48602 p ≤ (-1 : Int) + d48498 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26019 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26023 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26025 (p : Pattern) (guard : d18875 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d763 p = 1 := by simpa only [d18875, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26024 p hg
    simpa only [d18875, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18875, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d18875, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26026 (p : Pattern) (guard : d18876 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d18876, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d18876, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18875 p = 1 := by simpa only [d18876, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26025 p hg
    simpa only [d18876, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26027 (p : Pattern) (guard : d18877 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d18874 p = 1 := by simpa only [d18877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26022 p hg
    simpa only [d18877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18876 p = 1 := by simpa only [d18877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26026 p hg
    simpa only [d18877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26028 (p : Pattern) (guard : d18878 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d18872 p = 1 := by simpa only [d18878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26017 p hg
    simpa only [d18878, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18877 p = 1 := by simpa only [d18878, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26027 p hg
    simpa only [d18878, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26029 (p : Pattern) (guard : d188016 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16283 p = 1 := by simpa only [d188016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25956 p hg
    simpa only [d188016, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18878 p = 1 := by simpa only [d188016, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26028 p hg
    simpa only [d188016, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26030 (p : Pattern) (guard : d188017 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188016 p = 1 := by simpa only [d188017, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26029 p hg
    simpa only [d188017, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188017, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d188017, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26031 (p : Pattern) (guard : d188018 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188018, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d188018, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188017 p = 1 := by simpa only [d188018, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26030 p hg
    simpa only [d188018, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26032 (p : Pattern) (guard : d767 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25954 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26033 (p : Pattern) (guard : d16232 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16231 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25955 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26032 p hg
    simpa only [d16232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26034 (p : Pattern) (guard : d18884 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d18876 p = 1 := by simpa only [d18884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26026 p hg
    simpa only [d18884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d18884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26035 (p : Pattern) (guard : d18885 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d18877 p = 1 := by simpa only [d18885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26027 p hg
    simpa only [d18885, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18884 p = 1 := by simpa only [d18885, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26034 p hg
    simpa only [d18885, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26036 (p : Pattern) (guard : d188019 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d16232 p = 1 := by simpa only [d188019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26033 p hg
    simpa only [d188019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18885 p = 1 := by simpa only [d188019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26035 p hg
    simpa only [d188019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26037 (p : Pattern) (guard : d188020 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188019 p = 1 := by simpa only [d188020, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26036 p hg
    simpa only [d188020, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188020, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d188020, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26038 (p : Pattern) (guard : d188021 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188021, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d188021, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188020 p = 1 := by simpa only [d188021, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26037 p hg
    simpa only [d188021, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26039 (p : Pattern) (guard : d188022 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188018 p = 1 := by simpa only [d188022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26031 p hg
    simpa only [d188022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188021 p = 1 := by simpa only [d188022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26038 p hg
    simpa only [d188022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26040 (p : Pattern) (guard : d188023 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188022 p = 1 := by simpa only [d188023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26039 p hg
    simpa only [d188023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26041 (p : Pattern) (guard : d188024 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188023 p = 1 := by simpa only [d188024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26040 p hg
    simpa only [d188024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26042 (p : Pattern) (guard : d188025 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188024 p = 1 := by simpa only [d188025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26041 p hg
    simpa only [d188025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26043 (p : Pattern) (guard : d772 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26032 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26044 (p : Pattern) (guard : d18894 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d18884 p = 1 := by simpa only [d18894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26034 p hg
    simpa only [d18894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25493 p hg
    simpa only [d18894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26045 (p : Pattern) (guard : d188026 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d188026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26043 p hg
    simpa only [d188026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18894 p = 1 := by simpa only [d188026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26044 p hg
    simpa only [d188026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26046 (p : Pattern) (guard : d188027 p = 1) : d48705 p ≤ (-1 : Int) + d188506 p := by
  cases selected : p 116 with
  | false =>
    have hg : d188026 p = 1 := by simpa only [d188027, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26045 p hg
    simpa only [d188027, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188027, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25527 p hg
    simpa only [d188027, d48705, d188506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26047 (p : Pattern) (guard : d188028 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188028, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25461 p hg
    simpa only [d188028, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188027 p = 1 := by simpa only [d188028, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26046 p hg
    simpa only [d188028, d48706, d188507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26048 (p : Pattern) (guard : d188029 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188021 p = 1 := by simpa only [d188029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26038 p hg
    simpa only [d188029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188028 p = 1 := by simpa only [d188029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26047 p hg
    simpa only [d188029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26049 (p : Pattern) (guard : d188030 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188029 p = 1 := by simpa only [d188030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26048 p hg
    simpa only [d188030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26050 (p : Pattern) (guard : d188031 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188030 p = 1 := by simpa only [d188031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26049 p hg
    simpa only [d188031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26051 (p : Pattern) (guard : d188032 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188031 p = 1 := by simpa only [d188032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26050 p hg
    simpa only [d188032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26052 (p : Pattern) (guard : d188033 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d188025 p = 1 := by simpa only [d188033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26042 p hg
    simpa only [d188033, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188032 p = 1 := by simpa only [d188033, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26051 p hg
    simpa only [d188033, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26053 (p : Pattern) (guard : d188034 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d188033 p = 1 := by simpa only [d188034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26052 p hg
    simpa only [d188034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26054 (p : Pattern) (guard : d188035 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188021 p = 1 := by simpa only [d188035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26038 p hg
    simpa only [d188035, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188035, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188035, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26055 (p : Pattern) (guard : d188036 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188035 p = 1 := by simpa only [d188036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26054 p hg
    simpa only [d188036, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188036, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188036, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26056 (p : Pattern) (guard : d188037 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188036 p = 1 := by simpa only [d188037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26055 p hg
    simpa only [d188037, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188037, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188037, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26057 (p : Pattern) (guard : d188038 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188037 p = 1 := by simpa only [d188038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26056 p hg
    simpa only [d188038, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188038, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188038, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26058 (p : Pattern) (guard : d188039 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d188038 p = 1 := by simpa only [d188039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26057 p hg
    simpa only [d188039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26059 (p : Pattern) (guard : d188040 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d188039 p = 1 := by simpa only [d188040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26058 p hg
    simpa only [d188040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26060 (p : Pattern) (guard : d188041 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d188034 p = 1 := by simpa only [d188041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26053 p hg
    simpa only [d188041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188040 p = 1 := by simpa only [d188041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26059 p hg
    simpa only [d188041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26061 (p : Pattern) (guard : d188042 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188041 p = 1 := by simpa only [d188042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26060 p hg
    simpa only [d188042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26062 (p : Pattern) (guard : d188043 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188042 p = 1 := by simpa only [d188043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26061 p hg
    simpa only [d188043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26063 (p : Pattern) (guard : d188044 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188044, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25459 p hg
    simpa only [d188044, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188043 p = 1 := by simpa only [d188044, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26062 p hg
    simpa only [d188044, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26064 (p : Pattern) (guard : d188045 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188044 p = 1 := by simpa only [d188045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26063 p hg
    simpa only [d188045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26065 (p : Pattern) (guard : d188046 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 113 with
  | false =>
    have hg : d188028 p = 1 := by simpa only [d188046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26047 p hg
    simpa only [d188046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26066 (p : Pattern) (guard : d188047 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 96 with
  | false =>
    have hg : d188046 p = 1 := by simpa only [d188047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26065 p hg
    simpa only [d188047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26067 (p : Pattern) (guard : d188048 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 95 with
  | false =>
    have hg : d188047 p = 1 := by simpa only [d188048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26066 p hg
    simpa only [d188048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26068 (p : Pattern) (guard : d188049 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 93 with
  | false =>
    have hg : d188048 p = 1 := by simpa only [d188049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26067 p hg
    simpa only [d188049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26069 (p : Pattern) (guard : d188050 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 91 with
  | false =>
    have hg : d188049 p = 1 := by simpa only [d188050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26068 p hg
    simpa only [d188050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26070 (p : Pattern) (guard : d188051 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188050 p = 1 := by simpa only [d188051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26069 p hg
    simpa only [d188051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26071 (p : Pattern) (guard : d188052 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 89 with
  | false =>
    have hg : d188051 p = 1 := by simpa only [d188052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26070 p hg
    simpa only [d188052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26072 (p : Pattern) (guard : d188053 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188052 p = 1 := by simpa only [d188053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26071 p hg
    simpa only [d188053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26073 (p : Pattern) (guard : d188054 p = 1) : d48706 p ≤ (-1 : Int) + d188507 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25460 p hg
    simpa only [d188054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188053 p = 1 := by simpa only [d188054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26072 p hg
    simpa only [d188054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26074 (p : Pattern) (guard : d188055 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188055, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25459 p hg
    simpa only [d188055, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188054 p = 1 := by simpa only [d188055, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26073 p hg
    simpa only [d188055, d48707, d188508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26075 (p : Pattern) (guard : d188056 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188055 p = 1 := by simpa only [d188056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26074 p hg
    simpa only [d188056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26076 (p : Pattern) (guard : d188057 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 69 with
  | false =>
    have hg : d188045 p = 1 := by simpa only [d188057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26064 p hg
    simpa only [d188057, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188056 p = 1 := by simpa only [d188057, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26075 p hg
    simpa only [d188057, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26077 (p : Pattern) (guard : d188058 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 51 with
  | false =>
    have hg : d188057 p = 1 := by simpa only [d188058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26076 p hg
    simpa only [d188058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26078 (p : Pattern) (guard : d188059 p = 1) : d48707 p ≤ (-1 : Int) + d188508 p := by
  cases selected : p 50 with
  | false =>
    have hg : d188058 p = 1 := by simpa only [d188059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26077 p hg
    simpa only [d188059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25458 p hg
    simpa only [d188059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26079 (p : Pattern) (guard : d188060 p = 1) : d48748 p ≤ (-1 : Int) + d188517 p := by
  cases selected : p 49 with
  | false =>
    have hg : d188059 p = 1 := by simpa only [d188060, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26078 p hg
    simpa only [d188060, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d188060, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25544 p hg
    simpa only [d188060, d48748, d188517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26080 (p : Pattern) (guard : d188061 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188061, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25457 p hg
    simpa only [d188061, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188060 p = 1 := by simpa only [d188061, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26079 p hg
    simpa only [d188061, d48749, d188518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26081 (p : Pattern) (guard : d188062 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188061 p = 1 := by simpa only [d188062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26080 p hg
    simpa only [d188062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26082 (p : Pattern) (guard : d188063 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188062 p = 1 := by simpa only [d188063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26081 p hg
    simpa only [d188063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26083 (p : Pattern) (guard : d188064 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188063 p = 1 := by simpa only [d188064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26082 p hg
    simpa only [d188064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26084 (p : Pattern) (guard : d188065 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188064 p = 1 := by simpa only [d188065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26083 p hg
    simpa only [d188065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26085 (p : Pattern) (guard : d188066 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188065 p = 1 := by simpa only [d188066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26084 p hg
    simpa only [d188066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26086 (p : Pattern) (guard : d188067 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188067, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188066 p = 1 := by simpa only [d188067, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26085 p hg
    simpa only [d188067, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26087 (p : Pattern) (guard : d188068 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d188068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25456 p hg
    simpa only [d188068, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188067 p = 1 := by simpa only [d188068, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26086 p hg
    simpa only [d188068, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26088 (p : Pattern) (guard : d188069 p = 1) : d48749 p ≤ (-1 : Int) + d188518 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d188015 p = 1 := by simpa only [d188069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25884 p hg
    simpa only [d188069, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d188068 p = 1 := by simpa only [d188069, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26087 p hg
    simpa only [d188069, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26089 (p : Pattern) (guard : d1199 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25885 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26090 (p : Pattern) (guard : d1200 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1199 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26089 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26091 (p : Pattern) (guard : d1201 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1200 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26090 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26092 (p : Pattern) (guard : d1202 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26091 p hg
    simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d823 p = 1 := by simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25888 p hg
    simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26093 (p : Pattern) (guard : d1203 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25891 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26094 (p : Pattern) (guard : d1204 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1203 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26093 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26095 (p : Pattern) (guard : d1205 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1204 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26094 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26096 (p : Pattern) (guard : d1206 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1205 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26095 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d829 p = 1 := by simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25894 p hg
    simpa only [d1206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26097 (p : Pattern) (guard : d1207 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1202 p = 1 := by simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26092 p hg
    simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1206 p = 1 := by simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26096 p hg
    simpa only [d1207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26098 (p : Pattern) (guard : d1208 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1207 p = 1 := by simpa only [d1208, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26097 p hg
    simpa only [d1208, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1208, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d1208, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26099 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (-1 : Int) + d4 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare26100 (p : Pattern) (guard : d1084 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26099 p hg
    simpa only [d1084, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25553 p hg
    simpa only [d1084, d47630, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26101 (p : Pattern) (guard : d1085 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26100 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26102 (p : Pattern) (guard : d1086 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26101 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26103 (p : Pattern) (guard : d1087 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26102 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26104 (p : Pattern) (guard : d1088 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25726 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26103 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26105 (p : Pattern) (guard : d1089 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26104 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26106 (p : Pattern) (guard : d1090 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25888 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1089 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26105 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26107 (p : Pattern) (guard : d1091 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1090 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26106 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25895 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26108 (p : Pattern) (guard : d1092 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1091 p = 1 := by simpa only [d1092, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26107 p hg
    simpa only [d1092, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d1092, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26109 (p : Pattern) (guard : d1209 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1208 p = 1 := by simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26098 p hg
    simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1092 p = 1 := by simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26108 p hg
    simpa only [d1209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26110 (p : Pattern) (guard : d1210 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1209 p = 1 := by simpa only [d1210, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26109 p hg
    simpa only [d1210, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1210, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d1210, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26111 (p : Pattern) (guard : d1211 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1210 p = 1 := by simpa only [d1211, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26110 p hg
    simpa only [d1211, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1211, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d1211, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26112 (p : Pattern) (guard : d1212 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1212, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d1212, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1211 p = 1 := by simpa only [d1212, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26111 p hg
    simpa only [d1212, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26113 (p : Pattern) (guard : d1213 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1212 p = 1 := by simpa only [d1213, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26112 p hg
    simpa only [d1213, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1213, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d1213, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26114 (p : Pattern) (guard : d9749 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9582 p = 1 := by simpa only [d9749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25910 p hg
    simpa only [d9749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26115 (p : Pattern) (guard : d9750 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9749 p = 1 := by simpa only [d9750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26114 p hg
    simpa only [d9750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26116 (p : Pattern) (guard : d9751 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9750 p = 1 := by simpa only [d9751, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26115 p hg
    simpa only [d9751, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9751, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d9751, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26117 (p : Pattern) (guard : d9752 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d9752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26108 p hg
    simpa only [d9752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9751 p = 1 := by simpa only [d9752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26116 p hg
    simpa only [d9752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26118 (p : Pattern) (guard : d9753 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9752 p = 1 := by simpa only [d9753, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26117 p hg
    simpa only [d9753, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9753, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d9753, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26119 (p : Pattern) (guard : d9755 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9753 p = 1 := by simpa only [d9755, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26118 p hg
    simpa only [d9755, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9755, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d9755, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26120 (p : Pattern) (guard : d16507 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16507, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d16507, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9755 p = 1 := by simpa only [d16507, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26119 p hg
    simpa only [d16507, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26121 (p : Pattern) (guard : d16508 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16507 p = 1 := by simpa only [d16508, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26120 p hg
    simpa only [d16508, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16508, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d16508, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26122 (p : Pattern) (guard : d16509 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1213 p = 1 := by simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26113 p hg
    simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16508 p = 1 := by simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26121 p hg
    simpa only [d16509, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26123 (p : Pattern) (guard : d9759 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d9759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25888 p hg
    simpa only [d9759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26124 (p : Pattern) (guard : d9760 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9759 p = 1 := by simpa only [d9760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26123 p hg
    simpa only [d9760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26125 (p : Pattern) (guard : d9761 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9760 p = 1 := by simpa only [d9761, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26124 p hg
    simpa only [d9761, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9761, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d9761, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26126 (p : Pattern) (guard : d9762 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9761 p = 1 := by simpa only [d9762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26125 p hg
    simpa only [d9762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9751 p = 1 := by simpa only [d9762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26116 p hg
    simpa only [d9762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26127 (p : Pattern) (guard : d9763 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9762 p = 1 := by simpa only [d9763, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26126 p hg
    simpa only [d9763, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9763, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d9763, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26128 (p : Pattern) (guard : d9765 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9763 p = 1 := by simpa only [d9765, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26127 p hg
    simpa only [d9765, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9765, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d9765, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26129 (p : Pattern) (guard : d14836 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14836, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d14836, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9765 p = 1 := by simpa only [d14836, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26128 p hg
    simpa only [d14836, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26130 (p : Pattern) (guard : d14837 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14836 p = 1 := by simpa only [d14837, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26129 p hg
    simpa only [d14837, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14837, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d14837, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26131 (p : Pattern) (guard : d9768 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d9768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26105 p hg
    simpa only [d9768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9582 p = 1 := by simpa only [d9768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25910 p hg
    simpa only [d9768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26132 (p : Pattern) (guard : d9769 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9768 p = 1 := by simpa only [d9769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26131 p hg
    simpa only [d9769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26133 (p : Pattern) (guard : d9770 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9769 p = 1 := by simpa only [d9770, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26132 p hg
    simpa only [d9770, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9770, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d9770, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26134 (p : Pattern) (guard : d9771 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26102 p hg
    simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26135 (p : Pattern) (guard : d9772 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d9580 p = 1 := by simpa only [d9772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25908 p hg
    simpa only [d9772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9771 p = 1 := by simpa only [d9772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26134 p hg
    simpa only [d9772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26136 (p : Pattern) (guard : d9773 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d9772 p = 1 := by simpa only [d9773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26135 p hg
    simpa only [d9773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26137 (p : Pattern) (guard : d9774 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d9773 p = 1 := by simpa only [d9774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26136 p hg
    simpa only [d9774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25746 p hg
    simpa only [d9774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26138 (p : Pattern) (guard : d9775 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9774 p = 1 := by simpa only [d9775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26137 p hg
    simpa only [d9775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26139 (p : Pattern) (guard : d9776 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9775 p = 1 := by simpa only [d9776, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26138 p hg
    simpa only [d9776, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9776, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d9776, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26140 (p : Pattern) (guard : d9777 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9770 p = 1 := by simpa only [d9777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26133 p hg
    simpa only [d9777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9776 p = 1 := by simpa only [d9777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26139 p hg
    simpa only [d9777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26141 (p : Pattern) (guard : d9778 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9777 p = 1 := by simpa only [d9778, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26140 p hg
    simpa only [d9778, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9778, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d9778, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26142 (p : Pattern) (guard : d9780 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9778 p = 1 := by simpa only [d9780, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26141 p hg
    simpa only [d9780, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9780, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d9780, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26143 (p : Pattern) (guard : d14758 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14758, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d14758, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9780 p = 1 := by simpa only [d14758, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26142 p hg
    simpa only [d14758, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26144 (p : Pattern) (guard : d14759 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14758 p = 1 := by simpa only [d14759, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26143 p hg
    simpa only [d14759, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14759, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d14759, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26145 (p : Pattern) (guard : d16510 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14837 p = 1 := by simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26130 p hg
    simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14759 p = 1 := by simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26144 p hg
    simpa only [d16510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26146 (p : Pattern) (guard : d16511 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16509 p = 1 := by simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26122 p hg
    simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16510 p = 1 := by simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26145 p hg
    simpa only [d16511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26147 (p : Pattern) (guard : d1093 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26102 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25470 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26148 (p : Pattern) (guard : d1094 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25629 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26147 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26149 (p : Pattern) (guard : d1095 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26148 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26150 (p : Pattern) (guard : d1096 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26105 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26149 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26151 (p : Pattern) (guard : d1097 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26150 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25735 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26152 (p : Pattern) (guard : d1098 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1097 p = 1 := by simpa only [d1098, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26151 p hg
    simpa only [d1098, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1098, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d1098, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26153 (p : Pattern) (guard : d1099 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26108 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1098 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26152 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26154 (p : Pattern) (guard : d1100 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26153 p hg
    simpa only [d1100, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d1100, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26155 (p : Pattern) (guard : d1101 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1100 p = 1 := by simpa only [d1101, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26154 p hg
    simpa only [d1101, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1101, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d1101, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26156 (p : Pattern) (guard : d1102 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1102, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d1102, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1102, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26155 p hg
    simpa only [d1102, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26157 (p : Pattern) (guard : d1103 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26156 p hg
    simpa only [d1103, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d1103, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26158 (p : Pattern) (guard : d9788 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d9788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26152 p hg
    simpa only [d9788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9776 p = 1 := by simpa only [d9788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26139 p hg
    simpa only [d9788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26159 (p : Pattern) (guard : d9789 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9788 p = 1 := by simpa only [d9789, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26158 p hg
    simpa only [d9789, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9789, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d9789, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26160 (p : Pattern) (guard : d9791 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9789 p = 1 := by simpa only [d9791, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26159 p hg
    simpa only [d9791, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9791, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d9791, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26161 (p : Pattern) (guard : d16438 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16438, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d16438, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9791 p = 1 := by simpa only [d16438, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26160 p hg
    simpa only [d16438, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26162 (p : Pattern) (guard : d16439 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d16438 p = 1 := by simpa only [d16439, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26161 p hg
    simpa only [d16439, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d16439, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d16439, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26163 (p : Pattern) (guard : d16440 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26157 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16439 p = 1 := by simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26162 p hg
    simpa only [d16440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26164 (p : Pattern) (guard : d9795 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26149 p hg
    simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9453 p = 1 := by simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25746 p hg
    simpa only [d9795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26165 (p : Pattern) (guard : d9796 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d134 p = 1 := by simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25559 p hg
    simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26166 (p : Pattern) (guard : d9797 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9795 p = 1 := by simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26164 p hg
    simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9796 p = 1 := by simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26165 p hg
    simpa only [d9797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26167 (p : Pattern) (guard : d9798 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9797 p = 1 := by simpa only [d9798, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26166 p hg
    simpa only [d9798, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9798, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d9798, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26168 (p : Pattern) (guard : d1115 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25471 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26169 (p : Pattern) (guard : d1116 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1115 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26168 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26170 (p : Pattern) (guard : d1117 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26169 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25473 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26171 (p : Pattern) (guard : d1118 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1117 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26170 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25474 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26172 (p : Pattern) (guard : d1119 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1118 p = 1 := by simpa only [d1119, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26171 p hg
    simpa only [d1119, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1119, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d1119, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26173 (p : Pattern) (guard : d9799 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9798 p = 1 := by simpa only [d9799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26167 p hg
    simpa only [d9799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d9799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26172 p hg
    simpa only [d9799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26174 (p : Pattern) (guard : d9800 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9799 p = 1 := by simpa only [d9800, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26173 p hg
    simpa only [d9800, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9800, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d9800, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26175 (p : Pattern) (guard : d9802 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9800 p = 1 := by simpa only [d9802, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26174 p hg
    simpa only [d9802, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9802, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d9802, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26176 (p : Pattern) (guard : d14763 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14763, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d14763, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9802 p = 1 := by simpa only [d14763, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26175 p hg
    simpa only [d14763, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26177 (p : Pattern) (guard : d14764 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14763 p = 1 := by simpa only [d14764, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26176 p hg
    simpa only [d14764, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14764, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d14764, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26178 (p : Pattern) (guard : d16441 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14759 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26144 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26177 p hg
    simpa only [d16441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26179 (p : Pattern) (guard : d16442 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16440 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26163 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16441 p = 1 := by simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26178 p hg
    simpa only [d16442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26180 (p : Pattern) (guard : d16512 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16511 p = 1 := by simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26146 p hg
    simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16442 p = 1 := by simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26179 p hg
    simpa only [d16512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26181 (p : Pattern) (guard : d16513 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16513, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16513, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16512 p = 1 := by simpa only [d16513, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26180 p hg
    simpa only [d16513, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26182 (p : Pattern) (guard : d16514 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16514, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16514, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16513 p = 1 := by simpa only [d16514, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26181 p hg
    simpa only [d16514, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26183 (p : Pattern) (guard : d9810 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d9810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26105 p hg
    simpa only [d9810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9773 p = 1 := by simpa only [d9810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26136 p hg
    simpa only [d9810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26184 (p : Pattern) (guard : d9811 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d9810 p = 1 := by simpa only [d9811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26183 p hg
    simpa only [d9811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d9811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26185 (p : Pattern) (guard : d9812 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9811 p = 1 := by simpa only [d9812, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26184 p hg
    simpa only [d9812, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9812, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d9812, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26186 (p : Pattern) (guard : d9813 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9812 p = 1 := by simpa only [d9813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26185 p hg
    simpa only [d9813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9776 p = 1 := by simpa only [d9813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26139 p hg
    simpa only [d9813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26187 (p : Pattern) (guard : d9814 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9813 p = 1 := by simpa only [d9814, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26186 p hg
    simpa only [d9814, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9814, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d9814, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26188 (p : Pattern) (guard : d9816 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9814 p = 1 := by simpa only [d9816, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26187 p hg
    simpa only [d9816, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9816, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d9816, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26189 (p : Pattern) (guard : d13022 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d13022, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d13022, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9816 p = 1 := by simpa only [d13022, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26188 p hg
    simpa only [d13022, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26190 (p : Pattern) (guard : d13023 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d13022 p = 1 := by simpa only [d13023, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26189 p hg
    simpa only [d13023, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d13023, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d13023, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26191 (p : Pattern) (guard : d16515 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d13023 p = 1 := by simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26190 p hg
    simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14764 p = 1 := by simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26177 p hg
    simpa only [d16515, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26192 (p : Pattern) (guard : d14765 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14764 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26177 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d14765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26193 (p : Pattern) (guard : d16516 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d16515 p = 1 := by simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26191 p hg
    simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26192 p hg
    simpa only [d16516, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26194 (p : Pattern) (guard : d16517 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26179 p hg
    simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16516 p = 1 := by simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26193 p hg
    simpa only [d16517, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26195 (p : Pattern) (guard : d16518 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16518, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16518, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16517 p = 1 := by simpa only [d16518, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26194 p hg
    simpa only [d16518, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26196 (p : Pattern) (guard : d16519 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16519, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16519, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16518 p = 1 := by simpa only [d16519, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26195 p hg
    simpa only [d16519, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26197 (p : Pattern) (guard : d16520 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16514 p = 1 := by simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26182 p hg
    simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16519 p = 1 := by simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26196 p hg
    simpa only [d16520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26198 (p : Pattern) (guard : d1104 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25557 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25471 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26199 (p : Pattern) (guard : d1105 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1104 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26198 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26200 (p : Pattern) (guard : d1106 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26149 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1105 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26199 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26201 (p : Pattern) (guard : d1107 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1106 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26200 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25560 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26202 (p : Pattern) (guard : d1108 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1107 p = 1 := by simpa only [d1108, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26201 p hg
    simpa only [d1108, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1108, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d1108, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26203 (p : Pattern) (guard : d1109 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26152 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1108 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26202 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26204 (p : Pattern) (guard : d1110 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26203 p hg
    simpa only [d1110, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d1110, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26205 (p : Pattern) (guard : d1111 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1110 p = 1 := by simpa only [d1111, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26204 p hg
    simpa only [d1111, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1111, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d1111, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26206 (p : Pattern) (guard : d1112 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d1112, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26205 p hg
    simpa only [d1112, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26207 (p : Pattern) (guard : d1113 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26206 p hg
    simpa only [d1113, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d1113, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26208 (p : Pattern) (guard : d1120 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1108 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26202 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26172 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26209 (p : Pattern) (guard : d1121 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26208 p hg
    simpa only [d1121, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d1121, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26210 (p : Pattern) (guard : d1122 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1121 p = 1 := by simpa only [d1122, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26209 p hg
    simpa only [d1122, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1122, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d1122, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26211 (p : Pattern) (guard : d1123 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1123, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d1123, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1122 p = 1 := by simpa only [d1123, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26210 p hg
    simpa only [d1123, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26212 (p : Pattern) (guard : d1124 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1123 p = 1 := by simpa only [d1124, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26211 p hg
    simpa only [d1124, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1124, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d1124, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26213 (p : Pattern) (guard : d1125 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1113 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26207 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1124 p = 1 := by simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26212 p hg
    simpa only [d1125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26214 (p : Pattern) (guard : d16443 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1125 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26213 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14765 p = 1 := by simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26192 p hg
    simpa only [d16443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26215 (p : Pattern) (guard : d16444 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16442 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26179 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16443 p = 1 := by simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26214 p hg
    simpa only [d16444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26216 (p : Pattern) (guard : d16445 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16445, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16445, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16444 p = 1 := by simpa only [d16445, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26215 p hg
    simpa only [d16445, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26217 (p : Pattern) (guard : d16446 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16446, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16446, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16445 p = 1 := by simpa only [d16446, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26216 p hg
    simpa only [d16446, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26218 (p : Pattern) (guard : d5012 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d5011 p = 1 := by simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25744 p hg
    simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25471 p hg
    simpa only [d5012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26219 (p : Pattern) (guard : d5013 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5012 p = 1 := by simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26218 p hg
    simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d5013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26220 (p : Pattern) (guard : d5014 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26149 p hg
    simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5013 p = 1 := by simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26219 p hg
    simpa only [d5014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26221 (p : Pattern) (guard : d5015 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d5014 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26220 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25560 p hg
    simpa only [d5015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26222 (p : Pattern) (guard : d5016 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5015 p = 1 := by simpa only [d5016, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26221 p hg
    simpa only [d5016, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5016, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d5016, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26223 (p : Pattern) (guard : d5017 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d5016 p = 1 := by simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26222 p hg
    simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26172 p hg
    simpa only [d5017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26224 (p : Pattern) (guard : d5018 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5017 p = 1 := by simpa only [d5018, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26223 p hg
    simpa only [d5018, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5018, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d5018, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26225 (p : Pattern) (guard : d5019 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5018 p = 1 := by simpa only [d5019, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26224 p hg
    simpa only [d5019, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5019, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d5019, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26226 (p : Pattern) (guard : d5020 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d5020, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d5020, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5019 p = 1 := by simpa only [d5020, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26225 p hg
    simpa only [d5020, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26227 (p : Pattern) (guard : d5021 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5020 p = 1 := by simpa only [d5021, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26226 p hg
    simpa only [d5021, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5021, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d5021, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26228 (p : Pattern) (guard : d5022 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d5021 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26227 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d5022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26229 (p : Pattern) (guard : d1132 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26169 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25468 p hg
    simpa only [d1132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26230 (p : Pattern) (guard : d9841 p = 1) : d47630 p ≤ (-1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1132 p = 1 := by simpa only [d9841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26229 p hg
    simpa only [d9841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d9841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25474 p hg
    simpa only [d9841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26231 (p : Pattern) (guard : d9842 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d9841 p = 1 := by simpa only [d9842, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26230 p hg
    simpa only [d9842, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9842, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25476 p hg
    simpa only [d9842, d47652, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26232 (p : Pattern) (guard : d9843 p = 1) : d47652 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d9842 p = 1 := by simpa only [d9843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26231 p hg
    simpa only [d9843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25478 p hg
    simpa only [d9843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26233 (p : Pattern) (guard : d9844 p = 1) : d48407 p ≤ (-1 : Int) + d47619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d9843 p = 1 := by simpa only [d9844, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26232 p hg
    simpa only [d9844, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9844, d48407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25480 p hg
    simpa only [d9844, d48407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26234 (p : Pattern) (guard : d9846 p = 1) : d48571 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 162 with
  | false =>
    have hg : d9844 p = 1 := by simpa only [d9846, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26233 p hg
    simpa only [d9846, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9846, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25482 p hg
    simpa only [d9846, d48571, d48502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26235 (p : Pattern) (guard : d14770 p = 1) : d48698 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d14770, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25464 p hg
    simpa only [d14770, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9846 p = 1 := by simpa only [d14770, d48698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26234 p hg
    simpa only [d14770, d48698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26236 (p : Pattern) (guard : d14771 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 160 with
  | false =>
    have hg : d14770 p = 1 := by simpa only [d14771, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26235 p hg
    simpa only [d14771, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14771, d48701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25485 p hg
    simpa only [d14771, d48701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26237 (p : Pattern) (guard : d14772 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 159 with
  | false =>
    have hg : d14771 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26236 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25487 p hg
    simpa only [d14772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26238 (p : Pattern) (guard : d14773 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 158 with
  | false =>
    have hg : d5022 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26228 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14772 p = 1 := by simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26237 p hg
    simpa only [d14773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26239 (p : Pattern) (guard : d16447 p = 1) : d48701 p ≤ (-1 : Int) + d48502 p := by
  cases selected : p 157 with
  | false =>
    have hg : d16443 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26214 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14773 p = 1 := by simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26238 p hg
    simpa only [d16447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26240 (p : Pattern) (guard : d16448 p = 1) : d48702 p ≤ (-1 : Int) + d188503 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16448, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25463 p hg
    simpa only [d16448, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16447 p = 1 := by simpa only [d16448, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26239 p hg
    simpa only [d16448, d48702, d188503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26241 (p : Pattern) (guard : d16449 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d16449, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25462 p hg
    simpa only [d16449, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16448 p = 1 := by simpa only [d16449, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26240 p hg
    simpa only [d16449, d48703, d188504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26242 (p : Pattern) (guard : d16450 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 136 with
  | false =>
    have hg : d16446 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26217 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16449 p = 1 := by simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26241 p hg
    simpa only [d16450, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26243 (p : Pattern) (guard : d16521 p = 1) : d48703 p ≤ (-1 : Int) + d188504 p := by
  cases selected : p 135 with
  | false =>
    have hg : d16520 p = 1 := by simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26197 p hg
    simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d16450 p = 1 := by simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26242 p hg
    simpa only [d16521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26244 (p : Pattern) (guard : d1199 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d820 p = 1 := by simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25957 p hg
    simpa only [d1199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26245 (p : Pattern) (guard : d1200 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1199 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26244 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26246 (p : Pattern) (guard : d1201 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1200 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26245 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26247 (p : Pattern) (guard : d1202 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1201 p = 1 := by simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26246 p hg
    simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d823 p = 1 := by simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25960 p hg
    simpa only [d1202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26248 (p : Pattern) (guard : d1203 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d826 p = 1 := by simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25963 p hg
    simpa only [d1203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare26249 (p : Pattern) (guard : d1204 p = 1) : d47613 p ≤ (-1 : Int) + d47630 p := by
  cases selected : p 223 with
  | false =>
    have hg : d1203 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26248 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25500 p hg
    simpa only [d1204, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
