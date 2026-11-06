import NetHack.Soko22Hazard87.Compare089
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare22500 (p : Pattern) (guard : d179712 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179711 p = 1 := by simpa only [d179712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22499 p hg
    simpa only [d179712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22501 (p : Pattern) (guard : d179713 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179712 p = 1 := by simpa only [d179713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22500 p hg
    simpa only [d179713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22502 (p : Pattern) (guard : d179714 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179713 p = 1 := by simpa only [d179714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22501 p hg
    simpa only [d179714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22503 (p : Pattern) (guard : d179715 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179714 p = 1 := by simpa only [d179715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22502 p hg
    simpa only [d179715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22504 (p : Pattern) (guard : d179716 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179715 p = 1 := by simpa only [d179716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22503 p hg
    simpa only [d179716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22505 (p : Pattern) (guard : d179717 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179716 p = 1 := by simpa only [d179717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22504 p hg
    simpa only [d179717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22506 (p : Pattern) (guard : d179718 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21615 p hg
    simpa only [d179718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179717 p = 1 := by simpa only [d179718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22505 p hg
    simpa only [d179718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22507 (p : Pattern) (guard : d179719 p = 1) : d48388 p ≤ (1 : Int) + d47866 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d179459 p = 1 := by simpa only [d179719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22141 p hg
    simpa only [d179719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179718 p = 1 := by simpa only [d179719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22506 p hg
    simpa only [d179719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22508 (p : Pattern) (guard : d179726 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare22509 (p : Pattern) (guard : d179727 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179726 p = 1 := by simpa only [d179727, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22508 p hg
    simpa only [d179727, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179727, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21624 p hg
    simpa only [d179727, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22510 (p : Pattern) (guard : d179728 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179727 p = 1 := by simpa only [d179728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22509 p hg
    simpa only [d179728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22511 (p : Pattern) (guard : d179729 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179728 p = 1 := by simpa only [d179729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22510 p hg
    simpa only [d179729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22512 (p : Pattern) (guard : d179739 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare22513 (p : Pattern) (guard : d179740 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179739 p = 1 := by simpa only [d179740, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22512 p hg
    simpa only [d179740, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179740, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21624 p hg
    simpa only [d179740, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22514 (p : Pattern) (guard : d179741 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179740 p = 1 := by simpa only [d179741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22513 p hg
    simpa only [d179741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22515 (p : Pattern) (guard : d179742 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179741 p = 1 := by simpa only [d179742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22514 p hg
    simpa only [d179742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22516 (p : Pattern) (guard : d179743 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179729 p = 1 := by simpa only [d179743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22511 p hg
    simpa only [d179743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179742 p = 1 := by simpa only [d179743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22515 p hg
    simpa only [d179743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22517 (p : Pattern) (guard : d179744 p = 1) : d48326 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179744, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d179744, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179743 p = 1 := by simpa only [d179744, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22516 p hg
    simpa only [d179744, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22518 (p : Pattern) (guard : d179745 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179745, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d179745, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179744 p = 1 := by simpa only [d179745, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22517 p hg
    simpa only [d179745, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22519 (p : Pattern) (guard : d179746 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179742 p = 1 := by simpa only [d179746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22515 p hg
    simpa only [d179746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22520 (p : Pattern) (guard : d179747 p = 1) : d48326 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179747, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d179747, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179746 p = 1 := by simpa only [d179747, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22519 p hg
    simpa only [d179747, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22521 (p : Pattern) (guard : d179748 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179748, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d179748, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179747 p = 1 := by simpa only [d179748, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22520 p hg
    simpa only [d179748, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22522 (p : Pattern) (guard : d179749 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179745 p = 1 := by simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22518 p hg
    simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179748 p = 1 := by simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22521 p hg
    simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22523 (p : Pattern) (guard : d179750 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179748 p = 1 := by simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22521 p hg
    simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22524 (p : Pattern) (guard : d179751 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179749 p = 1 := by simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22522 p hg
    simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179750 p = 1 := by simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22523 p hg
    simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22525 (p : Pattern) (guard : d179752 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179751 p = 1 := by simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22524 p hg
    simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22526 (p : Pattern) (guard : d179753 p = 1) : d48338 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179752 p = 1 := by simpa only [d179753, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22525 p hg
    simpa only [d179753, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179753, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179753, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22527 (p : Pattern) (guard : d179754 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179754, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179754, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179753 p = 1 := by simpa only [d179754, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22526 p hg
    simpa only [d179754, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22528 (p : Pattern) (guard : d179755 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179750 p = 1 := by simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22523 p hg
    simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22529 (p : Pattern) (guard : d179756 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179755 p = 1 := by simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22528 p hg
    simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22530 (p : Pattern) (guard : d179757 p = 1) : d48338 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179756 p = 1 := by simpa only [d179757, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22529 p hg
    simpa only [d179757, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179757, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179757, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22531 (p : Pattern) (guard : d179758 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179758, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179758, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179757 p = 1 := by simpa only [d179758, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22530 p hg
    simpa only [d179758, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22532 (p : Pattern) (guard : d179759 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179754 p = 1 := by simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22527 p hg
    simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179758 p = 1 := by simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22531 p hg
    simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22533 (p : Pattern) (guard : d179760 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179759 p = 1 := by simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22532 p hg
    simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22534 (p : Pattern) (guard : d179761 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179760 p = 1 := by simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22533 p hg
    simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22535 (p : Pattern) (guard : d179762 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179761 p = 1 := by simpa only [d179762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22534 p hg
    simpa only [d179762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22536 (p : Pattern) (guard : d179763 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179758 p = 1 := by simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22531 p hg
    simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22537 (p : Pattern) (guard : d179764 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179763 p = 1 := by simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22536 p hg
    simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22538 (p : Pattern) (guard : d179765 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179764 p = 1 := by simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22537 p hg
    simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22539 (p : Pattern) (guard : d179766 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179765 p = 1 := by simpa only [d179766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22538 p hg
    simpa only [d179766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22540 (p : Pattern) (guard : d179767 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179762 p = 1 := by simpa only [d179767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22535 p hg
    simpa only [d179767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179766 p = 1 := by simpa only [d179767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22539 p hg
    simpa only [d179767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22541 (p : Pattern) (guard : d179768 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179767 p = 1 := by simpa only [d179768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22540 p hg
    simpa only [d179768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22542 (p : Pattern) (guard : d179769 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179768 p = 1 := by simpa only [d179769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22541 p hg
    simpa only [d179769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22543 (p : Pattern) (guard : d179770 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179769 p = 1 := by simpa only [d179770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22542 p hg
    simpa only [d179770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22544 (p : Pattern) (guard : d179771 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179770 p = 1 := by simpa only [d179771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22543 p hg
    simpa only [d179771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22545 (p : Pattern) (guard : d179772 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179772, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179772, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179771 p = 1 := by simpa only [d179772, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22544 p hg
    simpa only [d179772, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22546 (p : Pattern) (guard : d179773 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179772 p = 1 := by simpa only [d179773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22545 p hg
    simpa only [d179773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22547 (p : Pattern) (guard : d179774 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179773 p = 1 := by simpa only [d179774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22546 p hg
    simpa only [d179774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22548 (p : Pattern) (guard : d179745 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179745, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d179745, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179744 p = 1 := by simpa only [d179745, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22517 p hg
    simpa only [d179745, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22549 (p : Pattern) (guard : d179748 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179748, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d179748, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179747 p = 1 := by simpa only [d179748, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22520 p hg
    simpa only [d179748, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22550 (p : Pattern) (guard : d179749 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179745 p = 1 := by simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22548 p hg
    simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179748 p = 1 := by simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22549 p hg
    simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22551 (p : Pattern) (guard : d179750 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179748 p = 1 := by simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22549 p hg
    simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22552 (p : Pattern) (guard : d179751 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179749 p = 1 := by simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22550 p hg
    simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179750 p = 1 := by simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22551 p hg
    simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22553 (p : Pattern) (guard : d179752 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179751 p = 1 := by simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22552 p hg
    simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22554 (p : Pattern) (guard : d179753 p = 1) : d48329 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179752 p = 1 := by simpa only [d179753, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22553 p hg
    simpa only [d179753, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179753, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179753, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22555 (p : Pattern) (guard : d179754 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179754, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21648 p hg
    simpa only [d179754, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179753 p = 1 := by simpa only [d179754, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22554 p hg
    simpa only [d179754, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22556 (p : Pattern) (guard : d179755 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179750 p = 1 := by simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22551 p hg
    simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22557 (p : Pattern) (guard : d179756 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179755 p = 1 := by simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22556 p hg
    simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22558 (p : Pattern) (guard : d179757 p = 1) : d48329 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179756 p = 1 := by simpa only [d179757, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22557 p hg
    simpa only [d179757, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179757, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179757, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22559 (p : Pattern) (guard : d179758 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179758, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21648 p hg
    simpa only [d179758, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179757 p = 1 := by simpa only [d179758, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22558 p hg
    simpa only [d179758, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22560 (p : Pattern) (guard : d179759 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179754 p = 1 := by simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22555 p hg
    simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179758 p = 1 := by simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22559 p hg
    simpa only [d179759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22561 (p : Pattern) (guard : d179760 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179759 p = 1 := by simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22560 p hg
    simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22562 (p : Pattern) (guard : d179761 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179760 p = 1 := by simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22561 p hg
    simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22563 (p : Pattern) (guard : d179762 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179761 p = 1 := by simpa only [d179762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22562 p hg
    simpa only [d179762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22564 (p : Pattern) (guard : d179763 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179758 p = 1 := by simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22559 p hg
    simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22565 (p : Pattern) (guard : d179764 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179763 p = 1 := by simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22564 p hg
    simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22566 (p : Pattern) (guard : d179765 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179764 p = 1 := by simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22565 p hg
    simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22567 (p : Pattern) (guard : d179766 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179765 p = 1 := by simpa only [d179766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22566 p hg
    simpa only [d179766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22568 (p : Pattern) (guard : d179767 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179762 p = 1 := by simpa only [d179767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22563 p hg
    simpa only [d179767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179766 p = 1 := by simpa only [d179767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22567 p hg
    simpa only [d179767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22569 (p : Pattern) (guard : d179768 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179767 p = 1 := by simpa only [d179768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22568 p hg
    simpa only [d179768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22570 (p : Pattern) (guard : d179769 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179768 p = 1 := by simpa only [d179769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22569 p hg
    simpa only [d179769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22571 (p : Pattern) (guard : d179770 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179769 p = 1 := by simpa only [d179770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22570 p hg
    simpa only [d179770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22572 (p : Pattern) (guard : d179771 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179770 p = 1 := by simpa only [d179771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22571 p hg
    simpa only [d179771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22573 (p : Pattern) (guard : d179775 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179761 p = 1 := by simpa only [d179775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22534 p hg
    simpa only [d179775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22574 (p : Pattern) (guard : d179776 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179765 p = 1 := by simpa only [d179776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22538 p hg
    simpa only [d179776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22575 (p : Pattern) (guard : d179777 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179775 p = 1 := by simpa only [d179777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22573 p hg
    simpa only [d179777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179776 p = 1 := by simpa only [d179777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22574 p hg
    simpa only [d179777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22576 (p : Pattern) (guard : d179778 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179777 p = 1 := by simpa only [d179778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22575 p hg
    simpa only [d179778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22577 (p : Pattern) (guard : d179779 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179778 p = 1 := by simpa only [d179779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22576 p hg
    simpa only [d179779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22578 (p : Pattern) (guard : d179780 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179779 p = 1 := by simpa only [d179780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22577 p hg
    simpa only [d179780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22579 (p : Pattern) (guard : d179781 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179780 p = 1 := by simpa only [d179781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22578 p hg
    simpa only [d179781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22580 (p : Pattern) (guard : d179782 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179771 p = 1 := by simpa only [d179782, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22572 p hg
    simpa only [d179782, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179781 p = 1 := by simpa only [d179782, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22579 p hg
    simpa only [d179782, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22581 (p : Pattern) (guard : d179783 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179772 p = 1 := by simpa only [d179783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22545 p hg
    simpa only [d179783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179782 p = 1 := by simpa only [d179783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22580 p hg
    simpa only [d179783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22582 (p : Pattern) (guard : d179784 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179783 p = 1 := by simpa only [d179784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22581 p hg
    simpa only [d179784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22583 (p : Pattern) (guard : d179785 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179774 p = 1 := by simpa only [d179785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22547 p hg
    simpa only [d179785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179784 p = 1 := by simpa only [d179785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22582 p hg
    simpa only [d179785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22584 (p : Pattern) (guard : d179786 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179760 p = 1 := by simpa only [d179786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22533 p hg
    simpa only [d179786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22585 (p : Pattern) (guard : d179787 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179786 p = 1 := by simpa only [d179787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22584 p hg
    simpa only [d179787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22586 (p : Pattern) (guard : d179788 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179764 p = 1 := by simpa only [d179788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22537 p hg
    simpa only [d179788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22587 (p : Pattern) (guard : d179789 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179788 p = 1 := by simpa only [d179789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22586 p hg
    simpa only [d179789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22588 (p : Pattern) (guard : d179790 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179787 p = 1 := by simpa only [d179790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22585 p hg
    simpa only [d179790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179789 p = 1 := by simpa only [d179790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22587 p hg
    simpa only [d179790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22589 (p : Pattern) (guard : d179791 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179790 p = 1 := by simpa only [d179791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22588 p hg
    simpa only [d179791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22590 (p : Pattern) (guard : d179792 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179791 p = 1 := by simpa only [d179792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22589 p hg
    simpa only [d179792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22591 (p : Pattern) (guard : d179793 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179792 p = 1 := by simpa only [d179793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22590 p hg
    simpa only [d179793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22592 (p : Pattern) (guard : d179794 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179759 p = 1 := by simpa only [d179794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22532 p hg
    simpa only [d179794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22593 (p : Pattern) (guard : d179795 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179794 p = 1 := by simpa only [d179795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22592 p hg
    simpa only [d179795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22594 (p : Pattern) (guard : d179796 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179795 p = 1 := by simpa only [d179796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22593 p hg
    simpa only [d179796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22595 (p : Pattern) (guard : d179797 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179763 p = 1 := by simpa only [d179797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22536 p hg
    simpa only [d179797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22596 (p : Pattern) (guard : d179798 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179797 p = 1 := by simpa only [d179798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22595 p hg
    simpa only [d179798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22597 (p : Pattern) (guard : d179799 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179798 p = 1 := by simpa only [d179799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22596 p hg
    simpa only [d179799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22598 (p : Pattern) (guard : d179800 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179796 p = 1 := by simpa only [d179800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22594 p hg
    simpa only [d179800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179799 p = 1 := by simpa only [d179800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22597 p hg
    simpa only [d179800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22599 (p : Pattern) (guard : d179801 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179800 p = 1 := by simpa only [d179801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22598 p hg
    simpa only [d179801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22600 (p : Pattern) (guard : d179802 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179801 p = 1 := by simpa only [d179802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22599 p hg
    simpa only [d179802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22601 (p : Pattern) (guard : d179809 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare22602 (p : Pattern) (guard : d179810 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179809 p = 1 := by simpa only [d179810, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22601 p hg
    simpa only [d179810, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179810, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21624 p hg
    simpa only [d179810, d48313, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22603 (p : Pattern) (guard : d179811 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179810 p = 1 := by simpa only [d179811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22602 p hg
    simpa only [d179811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22604 (p : Pattern) (guard : d179812 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179811 p = 1 := by simpa only [d179812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22603 p hg
    simpa only [d179812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22605 (p : Pattern) (guard : d179813 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179812 p = 1 := by simpa only [d179813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22604 p hg
    simpa only [d179813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179729 p = 1 := by simpa only [d179813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22511 p hg
    simpa only [d179813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22606 (p : Pattern) (guard : d179814 p = 1) : d48326 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179814, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d179814, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179813 p = 1 := by simpa only [d179814, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22605 p hg
    simpa only [d179814, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22607 (p : Pattern) (guard : d179815 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179815, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d179815, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179814 p = 1 := by simpa only [d179815, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22606 p hg
    simpa only [d179815, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22608 (p : Pattern) (guard : d179816 p = 1) : d48313 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179729 p = 1 := by simpa only [d179816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22511 p hg
    simpa only [d179816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21622 p hg
    simpa only [d179816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22609 (p : Pattern) (guard : d179817 p = 1) : d48326 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179817, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21621 p hg
    simpa only [d179817, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179816 p = 1 := by simpa only [d179817, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22608 p hg
    simpa only [d179817, d48326, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22610 (p : Pattern) (guard : d179818 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179818, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21620 p hg
    simpa only [d179818, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179817 p = 1 := by simpa only [d179818, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22609 p hg
    simpa only [d179818, d48337, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22611 (p : Pattern) (guard : d179819 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179815 p = 1 := by simpa only [d179819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22607 p hg
    simpa only [d179819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179818 p = 1 := by simpa only [d179819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22610 p hg
    simpa only [d179819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22612 (p : Pattern) (guard : d179820 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179819 p = 1 := by simpa only [d179820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22611 p hg
    simpa only [d179820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179749 p = 1 := by simpa only [d179820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22522 p hg
    simpa only [d179820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22613 (p : Pattern) (guard : d179821 p = 1) : d48337 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179820 p = 1 := by simpa only [d179821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22612 p hg
    simpa only [d179821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21631 p hg
    simpa only [d179821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22614 (p : Pattern) (guard : d179822 p = 1) : d48338 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179821 p = 1 := by simpa only [d179822, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22613 p hg
    simpa only [d179822, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179822, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179822, d48338, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22615 (p : Pattern) (guard : d179823 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179823, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21619 p hg
    simpa only [d179823, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179822 p = 1 := by simpa only [d179823, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22614 p hg
    simpa only [d179823, d48339, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22616 (p : Pattern) (guard : d179824 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179823 p = 1 := by simpa only [d179824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22615 p hg
    simpa only [d179824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179754 p = 1 := by simpa only [d179824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22527 p hg
    simpa only [d179824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22617 (p : Pattern) (guard : d179825 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179824 p = 1 := by simpa only [d179825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22616 p hg
    simpa only [d179825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22618 (p : Pattern) (guard : d179826 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179825 p = 1 := by simpa only [d179826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22617 p hg
    simpa only [d179826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22619 (p : Pattern) (guard : d179827 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179826 p = 1 := by simpa only [d179827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22618 p hg
    simpa only [d179827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22620 (p : Pattern) (guard : d179828 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179827 p = 1 := by simpa only [d179828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22619 p hg
    simpa only [d179828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179762 p = 1 := by simpa only [d179828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22535 p hg
    simpa only [d179828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22621 (p : Pattern) (guard : d179829 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179828 p = 1 := by simpa only [d179829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22620 p hg
    simpa only [d179829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22622 (p : Pattern) (guard : d179830 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179754 p = 1 := by simpa only [d179830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22527 p hg
    simpa only [d179830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22623 (p : Pattern) (guard : d179831 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179830 p = 1 := by simpa only [d179831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22622 p hg
    simpa only [d179831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22624 (p : Pattern) (guard : d179832 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179831 p = 1 := by simpa only [d179832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22623 p hg
    simpa only [d179832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22625 (p : Pattern) (guard : d179833 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179832 p = 1 := by simpa only [d179833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22624 p hg
    simpa only [d179833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22626 (p : Pattern) (guard : d179834 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179833 p = 1 := by simpa only [d179834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22625 p hg
    simpa only [d179834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22627 (p : Pattern) (guard : d179835 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179834 p = 1 := by simpa only [d179835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22626 p hg
    simpa only [d179835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22628 (p : Pattern) (guard : d179836 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179829 p = 1 := by simpa only [d179836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22621 p hg
    simpa only [d179836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179835 p = 1 := by simpa only [d179836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22627 p hg
    simpa only [d179836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22629 (p : Pattern) (guard : d179837 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d179802 p = 1 := by simpa only [d179837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22600 p hg
    simpa only [d179837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179836 p = 1 := by simpa only [d179837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22628 p hg
    simpa only [d179837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22630 (p : Pattern) (guard : d179838 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d179793 p = 1 := by simpa only [d179838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22591 p hg
    simpa only [d179838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179837 p = 1 := by simpa only [d179838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22629 p hg
    simpa only [d179838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22631 (p : Pattern) (guard : d179839 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179839, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179839, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179838 p = 1 := by simpa only [d179839, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22630 p hg
    simpa only [d179839, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22632 (p : Pattern) (guard : d179786 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179760 p = 1 := by simpa only [d179786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22561 p hg
    simpa only [d179786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22633 (p : Pattern) (guard : d179787 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179786 p = 1 := by simpa only [d179787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22632 p hg
    simpa only [d179787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22634 (p : Pattern) (guard : d179788 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179764 p = 1 := by simpa only [d179788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22565 p hg
    simpa only [d179788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22635 (p : Pattern) (guard : d179789 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179788 p = 1 := by simpa only [d179789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22634 p hg
    simpa only [d179789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22636 (p : Pattern) (guard : d179790 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179787 p = 1 := by simpa only [d179790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22633 p hg
    simpa only [d179790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179789 p = 1 := by simpa only [d179790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22635 p hg
    simpa only [d179790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22637 (p : Pattern) (guard : d179791 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179790 p = 1 := by simpa only [d179791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22636 p hg
    simpa only [d179791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22638 (p : Pattern) (guard : d179792 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179791 p = 1 := by simpa only [d179792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22637 p hg
    simpa only [d179792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22639 (p : Pattern) (guard : d179793 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179792 p = 1 := by simpa only [d179793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22638 p hg
    simpa only [d179793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22640 (p : Pattern) (guard : d179794 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179759 p = 1 := by simpa only [d179794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22560 p hg
    simpa only [d179794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22641 (p : Pattern) (guard : d179795 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179794 p = 1 := by simpa only [d179795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22640 p hg
    simpa only [d179795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22642 (p : Pattern) (guard : d179796 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179795 p = 1 := by simpa only [d179796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22641 p hg
    simpa only [d179796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22643 (p : Pattern) (guard : d179797 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179763 p = 1 := by simpa only [d179797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22564 p hg
    simpa only [d179797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22644 (p : Pattern) (guard : d179798 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179797 p = 1 := by simpa only [d179798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22643 p hg
    simpa only [d179798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22645 (p : Pattern) (guard : d179799 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179798 p = 1 := by simpa only [d179799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22644 p hg
    simpa only [d179799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22646 (p : Pattern) (guard : d179800 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179796 p = 1 := by simpa only [d179800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22642 p hg
    simpa only [d179800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179799 p = 1 := by simpa only [d179800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22645 p hg
    simpa only [d179800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22647 (p : Pattern) (guard : d179801 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179800 p = 1 := by simpa only [d179801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22646 p hg
    simpa only [d179801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22648 (p : Pattern) (guard : d179802 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179801 p = 1 := by simpa only [d179802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22647 p hg
    simpa only [d179802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22649 (p : Pattern) (guard : d179815 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179815, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d179815, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179814 p = 1 := by simpa only [d179815, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22606 p hg
    simpa only [d179815, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22650 (p : Pattern) (guard : d179818 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179818, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21649 p hg
    simpa only [d179818, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179817 p = 1 := by simpa only [d179818, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22609 p hg
    simpa only [d179818, d48327, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22651 (p : Pattern) (guard : d179819 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179815 p = 1 := by simpa only [d179819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22649 p hg
    simpa only [d179819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179818 p = 1 := by simpa only [d179819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22650 p hg
    simpa only [d179819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22652 (p : Pattern) (guard : d179820 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179819 p = 1 := by simpa only [d179820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22651 p hg
    simpa only [d179820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179749 p = 1 := by simpa only [d179820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22550 p hg
    simpa only [d179820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22653 (p : Pattern) (guard : d179821 p = 1) : d48327 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179820 p = 1 := by simpa only [d179821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22652 p hg
    simpa only [d179821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21651 p hg
    simpa only [d179821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22654 (p : Pattern) (guard : d179822 p = 1) : d48329 p ≤ (1 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179821 p = 1 := by simpa only [d179822, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22653 p hg
    simpa only [d179822, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179822, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21635 p hg
    simpa only [d179822, d48329, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22655 (p : Pattern) (guard : d179823 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179823, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21648 p hg
    simpa only [d179823, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179822 p = 1 := by simpa only [d179823, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22654 p hg
    simpa only [d179823, d48330, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22656 (p : Pattern) (guard : d179824 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179823 p = 1 := by simpa only [d179824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22655 p hg
    simpa only [d179824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179754 p = 1 := by simpa only [d179824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22555 p hg
    simpa only [d179824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22657 (p : Pattern) (guard : d179825 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179824 p = 1 := by simpa only [d179825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22656 p hg
    simpa only [d179825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22658 (p : Pattern) (guard : d179826 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179825 p = 1 := by simpa only [d179826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22657 p hg
    simpa only [d179826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22659 (p : Pattern) (guard : d179827 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179826 p = 1 := by simpa only [d179827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22658 p hg
    simpa only [d179827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22660 (p : Pattern) (guard : d179828 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179827 p = 1 := by simpa only [d179828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22659 p hg
    simpa only [d179828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179762 p = 1 := by simpa only [d179828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22563 p hg
    simpa only [d179828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22661 (p : Pattern) (guard : d179829 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179828 p = 1 := by simpa only [d179829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22660 p hg
    simpa only [d179829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22662 (p : Pattern) (guard : d179830 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179754 p = 1 := by simpa only [d179830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22555 p hg
    simpa only [d179830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22663 (p : Pattern) (guard : d179831 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d179830 p = 1 := by simpa only [d179831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22662 p hg
    simpa only [d179831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22664 (p : Pattern) (guard : d179832 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d179831 p = 1 := by simpa only [d179832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22663 p hg
    simpa only [d179832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22665 (p : Pattern) (guard : d179833 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179832 p = 1 := by simpa only [d179833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22664 p hg
    simpa only [d179833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22666 (p : Pattern) (guard : d179834 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179833 p = 1 := by simpa only [d179834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22665 p hg
    simpa only [d179834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22667 (p : Pattern) (guard : d179835 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179834 p = 1 := by simpa only [d179835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22666 p hg
    simpa only [d179835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22668 (p : Pattern) (guard : d179836 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179829 p = 1 := by simpa only [d179836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22661 p hg
    simpa only [d179836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179835 p = 1 := by simpa only [d179836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22667 p hg
    simpa only [d179836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22669 (p : Pattern) (guard : d179837 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d179802 p = 1 := by simpa only [d179837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22648 p hg
    simpa only [d179837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179836 p = 1 := by simpa only [d179837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22668 p hg
    simpa only [d179837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22670 (p : Pattern) (guard : d179838 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d179793 p = 1 := by simpa only [d179838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22639 p hg
    simpa only [d179838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179837 p = 1 := by simpa only [d179838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22669 p hg
    simpa only [d179838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22671 (p : Pattern) (guard : d179840 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179786 p = 1 := by simpa only [d179840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22584 p hg
    simpa only [d179840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22672 (p : Pattern) (guard : d179841 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179788 p = 1 := by simpa only [d179841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22586 p hg
    simpa only [d179841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22673 (p : Pattern) (guard : d179842 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179840 p = 1 := by simpa only [d179842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22671 p hg
    simpa only [d179842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179841 p = 1 := by simpa only [d179842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22672 p hg
    simpa only [d179842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22674 (p : Pattern) (guard : d179843 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179842 p = 1 := by simpa only [d179843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22673 p hg
    simpa only [d179843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22675 (p : Pattern) (guard : d179844 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179843 p = 1 := by simpa only [d179844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22674 p hg
    simpa only [d179844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22676 (p : Pattern) (guard : d179845 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179844 p = 1 := by simpa only [d179845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22675 p hg
    simpa only [d179845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22677 (p : Pattern) (guard : d179846 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179795 p = 1 := by simpa only [d179846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22593 p hg
    simpa only [d179846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22678 (p : Pattern) (guard : d179847 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179798 p = 1 := by simpa only [d179847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22596 p hg
    simpa only [d179847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22679 (p : Pattern) (guard : d179848 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179846 p = 1 := by simpa only [d179848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22677 p hg
    simpa only [d179848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179847 p = 1 := by simpa only [d179848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22678 p hg
    simpa only [d179848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22680 (p : Pattern) (guard : d179849 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179848 p = 1 := by simpa only [d179849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22679 p hg
    simpa only [d179849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22681 (p : Pattern) (guard : d179850 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179849 p = 1 := by simpa only [d179850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22680 p hg
    simpa only [d179850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22682 (p : Pattern) (guard : d179851 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179826 p = 1 := by simpa only [d179851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22618 p hg
    simpa only [d179851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22683 (p : Pattern) (guard : d179852 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179851 p = 1 := by simpa only [d179852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22682 p hg
    simpa only [d179852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179775 p = 1 := by simpa only [d179852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22573 p hg
    simpa only [d179852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22684 (p : Pattern) (guard : d179853 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179852 p = 1 := by simpa only [d179853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22683 p hg
    simpa only [d179853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22685 (p : Pattern) (guard : d179854 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d179832 p = 1 := by simpa only [d179854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22624 p hg
    simpa only [d179854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22686 (p : Pattern) (guard : d179855 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179854 p = 1 := by simpa only [d179855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22685 p hg
    simpa only [d179855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22687 (p : Pattern) (guard : d179856 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d179855 p = 1 := by simpa only [d179856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22686 p hg
    simpa only [d179856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22688 (p : Pattern) (guard : d179857 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179853 p = 1 := by simpa only [d179857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22684 p hg
    simpa only [d179857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179856 p = 1 := by simpa only [d179857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22687 p hg
    simpa only [d179857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22689 (p : Pattern) (guard : d179858 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d179850 p = 1 := by simpa only [d179858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22681 p hg
    simpa only [d179858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179857 p = 1 := by simpa only [d179858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22688 p hg
    simpa only [d179858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22690 (p : Pattern) (guard : d179859 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d179845 p = 1 := by simpa only [d179859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22676 p hg
    simpa only [d179859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179858 p = 1 := by simpa only [d179859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22689 p hg
    simpa only [d179859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22691 (p : Pattern) (guard : d179860 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179838 p = 1 := by simpa only [d179860, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22670 p hg
    simpa only [d179860, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179859 p = 1 := by simpa only [d179860, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22690 p hg
    simpa only [d179860, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22692 (p : Pattern) (guard : d179861 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179839 p = 1 := by simpa only [d179861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22631 p hg
    simpa only [d179861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179860 p = 1 := by simpa only [d179861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22691 p hg
    simpa only [d179861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22693 (p : Pattern) (guard : d179862 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179766 p = 1 := by simpa only [d179862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22539 p hg
    simpa only [d179862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22694 (p : Pattern) (guard : d179863 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179862 p = 1 := by simpa only [d179863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22693 p hg
    simpa only [d179863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22695 (p : Pattern) (guard : d179864 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179863 p = 1 := by simpa only [d179864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22694 p hg
    simpa only [d179864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22696 (p : Pattern) (guard : d179865 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179864 p = 1 := by simpa only [d179865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22695 p hg
    simpa only [d179865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22697 (p : Pattern) (guard : d179866 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179865 p = 1 := by simpa only [d179866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22696 p hg
    simpa only [d179866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22698 (p : Pattern) (guard : d179867 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179771 p = 1 := by simpa only [d179867, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22572 p hg
    simpa only [d179867, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179866 p = 1 := by simpa only [d179867, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22697 p hg
    simpa only [d179867, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22699 (p : Pattern) (guard : d179862 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179766 p = 1 := by simpa only [d179862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22567 p hg
    simpa only [d179862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22700 (p : Pattern) (guard : d179863 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179862 p = 1 := by simpa only [d179863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22699 p hg
    simpa only [d179863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22701 (p : Pattern) (guard : d179864 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179863 p = 1 := by simpa only [d179864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22700 p hg
    simpa only [d179864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22702 (p : Pattern) (guard : d179865 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179864 p = 1 := by simpa only [d179865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22701 p hg
    simpa only [d179865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22703 (p : Pattern) (guard : d179866 p = 1) : d48330 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21617 p hg
    simpa only [d179866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179865 p = 1 := by simpa only [d179866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22702 p hg
    simpa only [d179866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22704 (p : Pattern) (guard : d179868 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d179776 p = 1 := by simpa only [d179868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22574 p hg
    simpa only [d179868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22705 (p : Pattern) (guard : d179869 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179868 p = 1 := by simpa only [d179869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22704 p hg
    simpa only [d179869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22706 (p : Pattern) (guard : d179870 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d179869 p = 1 := by simpa only [d179870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22705 p hg
    simpa only [d179870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22707 (p : Pattern) (guard : d179871 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179870 p = 1 := by simpa only [d179871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22706 p hg
    simpa only [d179871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22708 (p : Pattern) (guard : d179872 p = 1) : d48339 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21618 p hg
    simpa only [d179872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179871 p = 1 := by simpa only [d179872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22707 p hg
    simpa only [d179872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22709 (p : Pattern) (guard : d179873 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d179866 p = 1 := by simpa only [d179873, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22703 p hg
    simpa only [d179873, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179872 p = 1 := by simpa only [d179873, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22708 p hg
    simpa only [d179873, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22710 (p : Pattern) (guard : d179874 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d179867 p = 1 := by simpa only [d179874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22698 p hg
    simpa only [d179874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179873 p = 1 := by simpa only [d179874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22709 p hg
    simpa only [d179874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22711 (p : Pattern) (guard : d179875 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d179861 p = 1 := by simpa only [d179875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22692 p hg
    simpa only [d179875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179874 p = 1 := by simpa only [d179875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22710 p hg
    simpa only [d179875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22712 (p : Pattern) (guard : d179876 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d179875 p = 1 := by simpa only [d179876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22711 p hg
    simpa only [d179876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21616 p hg
    simpa only [d179876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22713 (p : Pattern) (guard : d179877 p = 1) : d48340 p ≤ (1 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d179785 p = 1 := by simpa only [d179877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22583 p hg
    simpa only [d179877, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179876 p = 1 := by simpa only [d179877, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22712 p hg
    simpa only [d179877, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22714 (p : Pattern) (guard : d179809 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare22715 (p : Pattern) (guard : d179810 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179809 p = 1 := by simpa only [d179810, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22714 p hg
    simpa only [d179810, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179810, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21684 p hg
    simpa only [d179810, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22716 (p : Pattern) (guard : d179811 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179810 p = 1 := by simpa only [d179811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22715 p hg
    simpa only [d179811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22717 (p : Pattern) (guard : d179812 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179811 p = 1 := by simpa only [d179812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22716 p hg
    simpa only [d179812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22718 (p : Pattern) (guard : d179726 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare22719 (p : Pattern) (guard : d179727 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179726 p = 1 := by simpa only [d179727, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22718 p hg
    simpa only [d179727, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179727, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21684 p hg
    simpa only [d179727, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22720 (p : Pattern) (guard : d179728 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179727 p = 1 := by simpa only [d179728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22719 p hg
    simpa only [d179728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22721 (p : Pattern) (guard : d179729 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179728 p = 1 := by simpa only [d179729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22720 p hg
    simpa only [d179729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22722 (p : Pattern) (guard : d179813 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179812 p = 1 := by simpa only [d179813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22717 p hg
    simpa only [d179813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179729 p = 1 := by simpa only [d179813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22721 p hg
    simpa only [d179813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22723 (p : Pattern) (guard : d179814 p = 1) : d48346 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179814, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d179814, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179813 p = 1 := by simpa only [d179814, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22722 p hg
    simpa only [d179814, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22724 (p : Pattern) (guard : d179815 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179815, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d179815, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179814 p = 1 := by simpa only [d179815, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22723 p hg
    simpa only [d179815, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22725 (p : Pattern) (guard : d179816 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179729 p = 1 := by simpa only [d179816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22721 p hg
    simpa only [d179816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22726 (p : Pattern) (guard : d179817 p = 1) : d48346 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179817, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d179817, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179816 p = 1 := by simpa only [d179817, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22725 p hg
    simpa only [d179817, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22727 (p : Pattern) (guard : d179818 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179818, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d179818, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179817 p = 1 := by simpa only [d179818, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22726 p hg
    simpa only [d179818, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22728 (p : Pattern) (guard : d179819 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179815 p = 1 := by simpa only [d179819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22724 p hg
    simpa only [d179819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179818 p = 1 := by simpa only [d179819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22727 p hg
    simpa only [d179819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22729 (p : Pattern) (guard : d179739 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare22730 (p : Pattern) (guard : d179740 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d179739 p = 1 := by simpa only [d179740, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22729 p hg
    simpa only [d179740, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179740, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21684 p hg
    simpa only [d179740, d48345, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22731 (p : Pattern) (guard : d179741 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179740 p = 1 := by simpa only [d179741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22730 p hg
    simpa only [d179741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22732 (p : Pattern) (guard : d179742 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d179741 p = 1 := by simpa only [d179742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22731 p hg
    simpa only [d179742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22733 (p : Pattern) (guard : d179743 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179729 p = 1 := by simpa only [d179743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22721 p hg
    simpa only [d179743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179742 p = 1 := by simpa only [d179743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22732 p hg
    simpa only [d179743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22734 (p : Pattern) (guard : d179744 p = 1) : d48346 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179744, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d179744, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179743 p = 1 := by simpa only [d179744, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22733 p hg
    simpa only [d179744, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22735 (p : Pattern) (guard : d179745 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179745, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d179745, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179744 p = 1 := by simpa only [d179745, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22734 p hg
    simpa only [d179745, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22736 (p : Pattern) (guard : d179746 p = 1) : d48345 p ≤ (1 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d179742 p = 1 := by simpa only [d179746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22732 p hg
    simpa only [d179746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21682 p hg
    simpa only [d179746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22737 (p : Pattern) (guard : d179747 p = 1) : d48346 p ≤ (1 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179747, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21681 p hg
    simpa only [d179747, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179746 p = 1 := by simpa only [d179747, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22736 p hg
    simpa only [d179747, d48346, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22738 (p : Pattern) (guard : d179748 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179748, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21680 p hg
    simpa only [d179748, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179747 p = 1 := by simpa only [d179748, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22737 p hg
    simpa only [d179748, d48354, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22739 (p : Pattern) (guard : d179749 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179745 p = 1 := by simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22735 p hg
    simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179748 p = 1 := by simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22738 p hg
    simpa only [d179749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22740 (p : Pattern) (guard : d179820 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179819 p = 1 := by simpa only [d179820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22728 p hg
    simpa only [d179820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179749 p = 1 := by simpa only [d179820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22739 p hg
    simpa only [d179820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22741 (p : Pattern) (guard : d179821 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179820 p = 1 := by simpa only [d179821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22740 p hg
    simpa only [d179821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22742 (p : Pattern) (guard : d179822 p = 1) : d48356 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179821 p = 1 := by simpa only [d179822, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22741 p hg
    simpa only [d179822, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179822, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21695 p hg
    simpa only [d179822, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22743 (p : Pattern) (guard : d179823 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179823, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d179823, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179822 p = 1 := by simpa only [d179823, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22742 p hg
    simpa only [d179823, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22744 (p : Pattern) (guard : d179750 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d179748 p = 1 := by simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22738 p hg
    simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22745 (p : Pattern) (guard : d179751 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d179749 p = 1 := by simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22739 p hg
    simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179750 p = 1 := by simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22744 p hg
    simpa only [d179751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22746 (p : Pattern) (guard : d179752 p = 1) : d48354 p ≤ (1 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d179751 p = 1 := by simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22745 p hg
    simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21691 p hg
    simpa only [d179752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22747 (p : Pattern) (guard : d179753 p = 1) : d48356 p ≤ (1 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d179752 p = 1 := by simpa only [d179753, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22746 p hg
    simpa only [d179753, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d179753, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21695 p hg
    simpa only [d179753, d48356, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22748 (p : Pattern) (guard : d179754 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d179754, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21679 p hg
    simpa only [d179754, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179753 p = 1 := by simpa only [d179754, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22747 p hg
    simpa only [d179754, d48357, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare22749 (p : Pattern) (guard : d179824 p = 1) : d48357 p ≤ (1 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d179823 p = 1 := by simpa only [d179824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22743 p hg
    simpa only [d179824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d179754 p = 1 := by simpa only [d179824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22748 p hg
    simpa only [d179824, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
