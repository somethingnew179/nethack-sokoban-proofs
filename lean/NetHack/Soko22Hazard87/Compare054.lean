import NetHack.Soko22Hazard87.Compare053
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare13500 (p : Pattern) (guard : d160805 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160804 p = 1 := by simpa only [d160805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13499 p hg
    simpa only [d160805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13501 (p : Pattern) (guard : d160806 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160805 p = 1 := by simpa only [d160806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13500 p hg
    simpa only [d160806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13502 (p : Pattern) (guard : d160807 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 71 with
  | false =>
    have hg : d160796 p = 1 := by simpa only [d160807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13493 p hg
    simpa only [d160807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160806 p = 1 := by simpa only [d160807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13501 p hg
    simpa only [d160807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13503 (p : Pattern) (guard : d160808 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 70 with
  | false =>
    have hg : d160797 p = 1 := by simpa only [d160808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13494 p hg
    simpa only [d160808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160807 p = 1 := by simpa only [d160808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13502 p hg
    simpa only [d160808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13504 (p : Pattern) (guard : d160809 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 69 with
  | false =>
    have hg : d160808 p = 1 := by simpa only [d160809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13503 p hg
    simpa only [d160809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d160809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13505 (p : Pattern) (guard : d161163 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 51 with
  | false =>
    have hg : d160809 p = 1 := by simpa only [d161163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13504 p hg
    simpa only [d161163, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161163, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161163, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13506 (p : Pattern) (guard : d161164 p = 1) : d47700 p ≤ (-2 : Int) + d159770 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161164, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161163 p = 1 := by simpa only [d161164, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13505 p hg
    simpa only [d161164, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13507 (p : Pattern) (guard : d2055 p = 1) : d47737 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2055, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12833 p hg
    simpa only [d2055, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2055, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9725 p hg
    simpa only [d2055, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13508 (p : Pattern) (guard : d2056 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2055 p = 1 := by simpa only [d2056, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13507 p hg
    simpa only [d2056, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2056, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12835 p hg
    simpa only [d2056, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13509 (p : Pattern) (guard : d160764 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2056 p = 1 := by simpa only [d160764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13508 p hg
    simpa only [d160764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13510 (p : Pattern) (guard : d160765 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160764 p = 1 := by simpa only [d160765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13509 p hg
    simpa only [d160765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13511 (p : Pattern) (guard : d2067 p = 1) : d47737 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2067, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12833 p hg
    simpa only [d2067, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2067, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9737 p hg
    simpa only [d2067, d47737, d47754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13512 (p : Pattern) (guard : d2068 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2067 p = 1 := by simpa only [d2068, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13511 p hg
    simpa only [d2068, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2068, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12835 p hg
    simpa only [d2068, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13513 (p : Pattern) (guard : d160766 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2068 p = 1 := by simpa only [d160766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13512 p hg
    simpa only [d160766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13514 (p : Pattern) (guard : d160767 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160766 p = 1 := by simpa only [d160767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13513 p hg
    simpa only [d160767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13515 (p : Pattern) (guard : d160768 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160765 p = 1 := by simpa only [d160768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13510 p hg
    simpa only [d160768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160767 p = 1 := by simpa only [d160768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13514 p hg
    simpa only [d160768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13516 (p : Pattern) (guard : d160769 p = 1) : d47756 p ≤ (-2 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160769, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12831 p hg
    simpa only [d160769, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160768 p = 1 := by simpa only [d160769, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13515 p hg
    simpa only [d160769, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13517 (p : Pattern) (guard : d160770 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160770, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12830 p hg
    simpa only [d160770, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160769 p = 1 := by simpa only [d160770, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13516 p hg
    simpa only [d160770, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13518 (p : Pattern) (guard : d160771 p = 1) : d47755 p ≤ (-2 : Int) + d47754 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160767 p = 1 := by simpa only [d160771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13514 p hg
    simpa only [d160771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12832 p hg
    simpa only [d160771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13519 (p : Pattern) (guard : d160772 p = 1) : d47756 p ≤ (-2 : Int) + d159771 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160772, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12831 p hg
    simpa only [d160772, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160771 p = 1 := by simpa only [d160772, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13518 p hg
    simpa only [d160772, d47756, d159771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13520 (p : Pattern) (guard : d160773 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160773, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12830 p hg
    simpa only [d160773, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160772 p = 1 := by simpa only [d160773, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13519 p hg
    simpa only [d160773, d47757, d159772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13521 (p : Pattern) (guard : d160774 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160770 p = 1 := by simpa only [d160774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13517 p hg
    simpa only [d160774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160773 p = 1 := by simpa only [d160774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13520 p hg
    simpa only [d160774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13522 (p : Pattern) (guard : d160775 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160773 p = 1 := by simpa only [d160775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13520 p hg
    simpa only [d160775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d160775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13523 (p : Pattern) (guard : d160776 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160774 p = 1 := by simpa only [d160776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13521 p hg
    simpa only [d160776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160775 p = 1 := by simpa only [d160776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13522 p hg
    simpa only [d160776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13524 (p : Pattern) (guard : d160777 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160776 p = 1 := by simpa only [d160777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13523 p hg
    simpa only [d160777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d160777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13525 (p : Pattern) (guard : d160778 p = 1) : d47765 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160777 p = 1 := by simpa only [d160778, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13524 p hg
    simpa only [d160778, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160778, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12846 p hg
    simpa only [d160778, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13526 (p : Pattern) (guard : d160779 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160779, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12829 p hg
    simpa only [d160779, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160778 p = 1 := by simpa only [d160779, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13525 p hg
    simpa only [d160779, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13527 (p : Pattern) (guard : d160780 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160775 p = 1 := by simpa only [d160780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13522 p hg
    simpa only [d160780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d160780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13528 (p : Pattern) (guard : d160781 p = 1) : d47757 p ≤ (-2 : Int) + d159772 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160780 p = 1 := by simpa only [d160781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13527 p hg
    simpa only [d160781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12842 p hg
    simpa only [d160781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13529 (p : Pattern) (guard : d160782 p = 1) : d47765 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160781 p = 1 := by simpa only [d160782, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13528 p hg
    simpa only [d160782, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160782, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12846 p hg
    simpa only [d160782, d47765, d159774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13530 (p : Pattern) (guard : d160783 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160783, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12829 p hg
    simpa only [d160783, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160782 p = 1 := by simpa only [d160783, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13529 p hg
    simpa only [d160783, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13531 (p : Pattern) (guard : d160784 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160779 p = 1 := by simpa only [d160784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13526 p hg
    simpa only [d160784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160783 p = 1 := by simpa only [d160784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13530 p hg
    simpa only [d160784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13532 (p : Pattern) (guard : d160785 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160784 p = 1 := by simpa only [d160785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13531 p hg
    simpa only [d160785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13533 (p : Pattern) (guard : d160786 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160785 p = 1 := by simpa only [d160786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13532 p hg
    simpa only [d160786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13534 (p : Pattern) (guard : d160800 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160786 p = 1 := by simpa only [d160800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13533 p hg
    simpa only [d160800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13535 (p : Pattern) (guard : d160788 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160783 p = 1 := by simpa only [d160788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13530 p hg
    simpa only [d160788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13536 (p : Pattern) (guard : d160789 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160788 p = 1 := by simpa only [d160789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13535 p hg
    simpa only [d160789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13537 (p : Pattern) (guard : d160790 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160789 p = 1 := by simpa only [d160790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13536 p hg
    simpa only [d160790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13538 (p : Pattern) (guard : d160801 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160790 p = 1 := by simpa only [d160801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13537 p hg
    simpa only [d160801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13539 (p : Pattern) (guard : d160802 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160800 p = 1 := by simpa only [d160802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13534 p hg
    simpa only [d160802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160801 p = 1 := by simpa only [d160802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13538 p hg
    simpa only [d160802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13540 (p : Pattern) (guard : d160803 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160802 p = 1 := by simpa only [d160803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13539 p hg
    simpa only [d160803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13541 (p : Pattern) (guard : d160804 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 89 with
  | false =>
    have hg : d160803 p = 1 := by simpa only [d160804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13540 p hg
    simpa only [d160804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13542 (p : Pattern) (guard : d160805 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160804 p = 1 := by simpa only [d160805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13541 p hg
    simpa only [d160805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13543 (p : Pattern) (guard : d160806 p = 1) : d47766 p ≤ (-2 : Int) + d159774 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12828 p hg
    simpa only [d160806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160805 p = 1 := by simpa only [d160806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13542 p hg
    simpa only [d160806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13544 (p : Pattern) (guard : d161165 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161165, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161165, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160806 p = 1 := by simpa only [d161165, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13543 p hg
    simpa only [d161165, d47767, d159775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13545 (p : Pattern) (guard : d161166 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161166, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161165 p = 1 := by simpa only [d161166, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13544 p hg
    simpa only [d161166, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13546 (p : Pattern) (guard : d161167 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 69 with
  | false =>
    have hg : d161166 p = 1 := by simpa only [d161167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13545 p hg
    simpa only [d161167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13547 (p : Pattern) (guard : d161168 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 51 with
  | false =>
    have hg : d161167 p = 1 := by simpa only [d161168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13546 p hg
    simpa only [d161168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13548 (p : Pattern) (guard : d161169 p = 1) : d47767 p ≤ (-2 : Int) + d159775 p := by
  cases selected : p 50 with
  | false =>
    have hg : d161168 p = 1 := by simpa only [d161169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13547 p hg
    simpa only [d161169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12827 p hg
    simpa only [d161169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13549 (p : Pattern) (guard : d161170 p = 1) : d47768 p ≤ (-2 : Int) + d159776 p := by
  cases selected : p 49 with
  | false =>
    have hg : d161164 p = 1 := by simpa only [d161170, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13506 p hg
    simpa only [d161170, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161169 p = 1 := by simpa only [d161170, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13548 p hg
    simpa only [d161170, d47768, d159776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13550 (p : Pattern) (guard : d2340 p = 1) : d47652 p ≤ (-2 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2340, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12869 p hg
    simpa only [d2340, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2052 p = 1 := by simpa only [d2340, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9885 p hg
    simpa only [d2340, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13551 (p : Pattern) (guard : d2341 p = 1) : d47798 p ≤ (-2 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2340 p = 1 := by simpa only [d2341, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13550 p hg
    simpa only [d2341, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2053 p = 1 := by simpa only [d2341, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9887 p hg
    simpa only [d2341, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13552 (p : Pattern) (guard : d2342 p = 1) : d47799 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2341 p = 1 := by simpa only [d2342, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13551 p hg
    simpa only [d2342, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2054 p = 1 := by simpa only [d2342, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9904 p hg
    simpa only [d2342, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13553 (p : Pattern) (guard : d2343 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2342 p = 1 := by simpa only [d2343, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13552 p hg
    simpa only [d2343, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2343, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12873 p hg
    simpa only [d2343, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13554 (p : Pattern) (guard : d160909 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2343 p = 1 := by simpa only [d160909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13553 p hg
    simpa only [d160909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13555 (p : Pattern) (guard : d160910 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160909 p = 1 := by simpa only [d160910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13554 p hg
    simpa only [d160910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13556 (p : Pattern) (guard : d2346 p = 1) : d47652 p ≤ (-2 : Int) + d47800 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2346, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12869 p hg
    simpa only [d2346, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2064 p = 1 := by simpa only [d2346, d47800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9914 p hg
    simpa only [d2346, d47800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13557 (p : Pattern) (guard : d2347 p = 1) : d47798 p ≤ (-2 : Int) + d47801 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2346 p = 1 := by simpa only [d2347, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13556 p hg
    simpa only [d2347, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2065 p = 1 := by simpa only [d2347, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9916 p hg
    simpa only [d2347, d47798, d47801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13558 (p : Pattern) (guard : d2348 p = 1) : d47799 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2347 p = 1 := by simpa only [d2348, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13557 p hg
    simpa only [d2348, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2066 p = 1 := by simpa only [d2348, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare9926 p hg
    simpa only [d2348, d47799, d47802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13559 (p : Pattern) (guard : d2349 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 160 with
  | false =>
    have hg : d2348 p = 1 := by simpa only [d2349, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13558 p hg
    simpa only [d2349, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2349, d47803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12873 p hg
    simpa only [d2349, d47803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13560 (p : Pattern) (guard : d160920 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2349 p = 1 := by simpa only [d160920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13559 p hg
    simpa only [d160920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13561 (p : Pattern) (guard : d160921 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 158 with
  | false =>
    have hg : d160920 p = 1 := by simpa only [d160921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13560 p hg
    simpa only [d160921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13562 (p : Pattern) (guard : d160922 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160910 p = 1 := by simpa only [d160922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13555 p hg
    simpa only [d160922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160921 p = 1 := by simpa only [d160922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13561 p hg
    simpa only [d160922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13563 (p : Pattern) (guard : d160923 p = 1) : d47804 p ≤ (-2 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160923, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12867 p hg
    simpa only [d160923, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160922 p = 1 := by simpa only [d160923, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13562 p hg
    simpa only [d160923, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13564 (p : Pattern) (guard : d160924 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160924, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12866 p hg
    simpa only [d160924, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160923 p = 1 := by simpa only [d160924, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13563 p hg
    simpa only [d160924, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13565 (p : Pattern) (guard : d160925 p = 1) : d47803 p ≤ (-2 : Int) + d47802 p := by
  cases selected : p 157 with
  | false =>
    have hg : d160921 p = 1 := by simpa only [d160925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13561 p hg
    simpa only [d160925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12868 p hg
    simpa only [d160925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13566 (p : Pattern) (guard : d160926 p = 1) : d47804 p ≤ (-2 : Int) + d159778 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160926, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12867 p hg
    simpa only [d160926, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160925 p = 1 := by simpa only [d160926, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13565 p hg
    simpa only [d160926, d47804, d159778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13567 (p : Pattern) (guard : d160927 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160927, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12866 p hg
    simpa only [d160927, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160926 p = 1 := by simpa only [d160927, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13566 p hg
    simpa only [d160927, d47805, d159779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13568 (p : Pattern) (guard : d160928 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160924 p = 1 := by simpa only [d160928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13564 p hg
    simpa only [d160928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160927 p = 1 := by simpa only [d160928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13567 p hg
    simpa only [d160928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13569 (p : Pattern) (guard : d160933 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 136 with
  | false =>
    have hg : d160927 p = 1 := by simpa only [d160933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13567 p hg
    simpa only [d160933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d160933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13570 (p : Pattern) (guard : d160934 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160928 p = 1 := by simpa only [d160934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13568 p hg
    simpa only [d160934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160933 p = 1 := by simpa only [d160934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13569 p hg
    simpa only [d160934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13571 (p : Pattern) (guard : d160935 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160934 p = 1 := by simpa only [d160935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13570 p hg
    simpa only [d160935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d160935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13572 (p : Pattern) (guard : d160936 p = 1) : d47807 p ≤ (-2 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160935 p = 1 := by simpa only [d160936, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13571 p hg
    simpa only [d160936, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160936, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12884 p hg
    simpa only [d160936, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13573 (p : Pattern) (guard : d160937 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160937, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d160937, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160936 p = 1 := by simpa only [d160937, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13572 p hg
    simpa only [d160937, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13574 (p : Pattern) (guard : d160942 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 135 with
  | false =>
    have hg : d160933 p = 1 := by simpa only [d160942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13569 p hg
    simpa only [d160942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d160942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13575 (p : Pattern) (guard : d160943 p = 1) : d47805 p ≤ (-2 : Int) + d159779 p := by
  cases selected : p 119 with
  | false =>
    have hg : d160942 p = 1 := by simpa only [d160943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13574 p hg
    simpa only [d160943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12880 p hg
    simpa only [d160943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13576 (p : Pattern) (guard : d160944 p = 1) : d47807 p ≤ (-2 : Int) + d159781 p := by
  cases selected : p 116 with
  | false =>
    have hg : d160943 p = 1 := by simpa only [d160944, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13575 p hg
    simpa only [d160944, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160944, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12884 p hg
    simpa only [d160944, d47807, d159781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13577 (p : Pattern) (guard : d160945 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d160945, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12786 p hg
    simpa only [d160945, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160944 p = 1 := by simpa only [d160945, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13576 p hg
    simpa only [d160945, d47808, d159782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13578 (p : Pattern) (guard : d160946 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160937 p = 1 := by simpa only [d160946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13573 p hg
    simpa only [d160946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160945 p = 1 := by simpa only [d160946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13577 p hg
    simpa only [d160946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13579 (p : Pattern) (guard : d160947 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160946 p = 1 := by simpa only [d160947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13578 p hg
    simpa only [d160947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13580 (p : Pattern) (guard : d160948 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160947 p = 1 := by simpa only [d160948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13579 p hg
    simpa only [d160948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13581 (p : Pattern) (guard : d160949 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160948 p = 1 := by simpa only [d160949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13580 p hg
    simpa only [d160949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13582 (p : Pattern) (guard : d160963 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 113 with
  | false =>
    have hg : d160945 p = 1 := by simpa only [d160963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13577 p hg
    simpa only [d160963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13583 (p : Pattern) (guard : d160964 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 96 with
  | false =>
    have hg : d160963 p = 1 := by simpa only [d160964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13582 p hg
    simpa only [d160964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13584 (p : Pattern) (guard : d160965 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 95 with
  | false =>
    have hg : d160964 p = 1 := by simpa only [d160965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13583 p hg
    simpa only [d160965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13585 (p : Pattern) (guard : d160966 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 93 with
  | false =>
    have hg : d160965 p = 1 := by simpa only [d160966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13584 p hg
    simpa only [d160966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d160966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d160966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13586 (p : Pattern) (guard : d161171 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 91 with
  | false =>
    have hg : d160949 p = 1 := by simpa only [d161171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13581 p hg
    simpa only [d161171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d160966 p = 1 := by simpa only [d161171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13585 p hg
    simpa only [d161171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13587 (p : Pattern) (guard : d161172 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161172, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161171 p = 1 := by simpa only [d161172, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13586 p hg
    simpa only [d161172, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13588 (p : Pattern) (guard : d161173 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 89 with
  | false =>
    have hg : d161172 p = 1 := by simpa only [d161173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13587 p hg
    simpa only [d161173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13589 (p : Pattern) (guard : d161174 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161174, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161173 p = 1 := by simpa only [d161174, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13588 p hg
    simpa only [d161174, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13590 (p : Pattern) (guard : d161175 p = 1) : d47808 p ≤ (-2 : Int) + d159782 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12865 p hg
    simpa only [d161175, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161174 p = 1 := by simpa only [d161175, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13589 p hg
    simpa only [d161175, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13591 (p : Pattern) (guard : d161176 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161176, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12785 p hg
    simpa only [d161176, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161175 p = 1 := by simpa only [d161176, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13590 p hg
    simpa only [d161176, d47809, d159783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13592 (p : Pattern) (guard : d161177 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161176 p = 1 := by simpa only [d161177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13591 p hg
    simpa only [d161177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13593 (p : Pattern) (guard : d161178 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 69 with
  | false =>
    have hg : d161177 p = 1 := by simpa only [d161178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13592 p hg
    simpa only [d161178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13594 (p : Pattern) (guard : d161179 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 51 with
  | false =>
    have hg : d161178 p = 1 := by simpa only [d161179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13593 p hg
    simpa only [d161179, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161179, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161179, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13595 (p : Pattern) (guard : d161180 p = 1) : d47809 p ≤ (-2 : Int) + d159783 p := by
  cases selected : p 50 with
  | false =>
    have hg : d161179 p = 1 := by simpa only [d161180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13594 p hg
    simpa only [d161180, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161180, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12864 p hg
    simpa only [d161180, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13596 (p : Pattern) (guard : d161181 p = 1) : d47865 p ≤ (-2 : Int) + d159794 p := by
  cases selected : p 49 with
  | false =>
    have hg : d161180 p = 1 := by simpa only [d161181, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13595 p hg
    simpa only [d161181, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161181, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12901 p hg
    simpa only [d161181, d47865, d159794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13597 (p : Pattern) (guard : d161182 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 48 with
  | false =>
    have hg : d161170 p = 1 := by simpa only [d161182, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13549 p hg
    simpa only [d161182, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161181 p = 1 := by simpa only [d161182, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13596 p hg
    simpa only [d161182, d47866, d159795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13598 (p : Pattern) (guard : d161183 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161182 p = 1 := by simpa only [d161183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13597 p hg
    simpa only [d161183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13599 (p : Pattern) (guard : d161184 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161183 p = 1 := by simpa only [d161184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13598 p hg
    simpa only [d161184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13600 (p : Pattern) (guard : d161185 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161184 p = 1 := by simpa only [d161185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13599 p hg
    simpa only [d161185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13601 (p : Pattern) (guard : d161186 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161186, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161185 p = 1 := by simpa only [d161186, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13600 p hg
    simpa only [d161186, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13602 (p : Pattern) (guard : d161187 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161186 p = 1 := by simpa only [d161187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13601 p hg
    simpa only [d161187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13603 (p : Pattern) (guard : d161188 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161187 p = 1 := by simpa only [d161188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13602 p hg
    simpa only [d161188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13604 (p : Pattern) (guard : d161189 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161188 p = 1 := by simpa only [d161189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13603 p hg
    simpa only [d161189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13605 (p : Pattern) (guard : d161190 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161189 p = 1 := by simpa only [d161190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13604 p hg
    simpa only [d161190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13606 (p : Pattern) (guard : d161191 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161190 p = 1 := by simpa only [d161191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13605 p hg
    simpa only [d161191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13607 (p : Pattern) (guard : d161192 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d161192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161192, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161191 p = 1 := by simpa only [d161192, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13606 p hg
    simpa only [d161192, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13608 (p : Pattern) (guard : d161193 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d161162 p = 1 := by simpa only [d161193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13456 p hg
    simpa only [d161193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d161192 p = 1 := by simpa only [d161193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13607 p hg
    simpa only [d161193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13609 (p : Pattern) (guard : d161194 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 260 with
  | false =>
    have hg : d161193 p = 1 := by simpa only [d161194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13608 p hg
    simpa only [d161194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13610 (p : Pattern) (guard : d161195 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 259 with
  | false =>
    have hg : d161194 p = 1 := by simpa only [d161195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13609 p hg
    simpa only [d161195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13611 (p : Pattern) (guard : d161196 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 258 with
  | false =>
    have hg : d161195 p = 1 := by simpa only [d161196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13610 p hg
    simpa only [d161196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13612 (p : Pattern) (guard : d161197 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 257 with
  | false =>
    have hg : d161196 p = 1 := by simpa only [d161197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13611 p hg
    simpa only [d161197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13613 (p : Pattern) (guard : d161198 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 256 with
  | false =>
    have hg : d161197 p = 1 := by simpa only [d161198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13612 p hg
    simpa only [d161198, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161198, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161198, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13614 (p : Pattern) (guard : d161199 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 255 with
  | false =>
    have hg : d161198 p = 1 := by simpa only [d161199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13613 p hg
    simpa only [d161199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13615 (p : Pattern) (guard : d161200 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 254 with
  | false =>
    have hg : d161199 p = 1 := by simpa only [d161200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13614 p hg
    simpa only [d161200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13616 (p : Pattern) (guard : d161201 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 253 with
  | false =>
    have hg : d161200 p = 1 := by simpa only [d161201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13615 p hg
    simpa only [d161201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13617 (p : Pattern) (guard : d161202 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 252 with
  | false =>
    have hg : d161201 p = 1 := by simpa only [d161202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13616 p hg
    simpa only [d161202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13618 (p : Pattern) (guard : d161203 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 251 with
  | false =>
    have hg : d161202 p = 1 := by simpa only [d161203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13617 p hg
    simpa only [d161203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13619 (p : Pattern) (guard : d161204 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 250 with
  | false =>
    have hg : d161203 p = 1 := by simpa only [d161204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13618 p hg
    simpa only [d161204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13620 (p : Pattern) (guard : d161205 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 249 with
  | false =>
    have hg : d161204 p = 1 := by simpa only [d161205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13619 p hg
    simpa only [d161205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13621 (p : Pattern) (guard : d161206 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 245 with
  | false =>
    have hg : d161205 p = 1 := by simpa only [d161206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13620 p hg
    simpa only [d161206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13622 (p : Pattern) (guard : d161207 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 200 with
  | false =>
    have hg : d161206 p = 1 := by simpa only [d161207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13621 p hg
    simpa only [d161207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13623 (p : Pattern) (guard : d161208 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 199 with
  | false =>
    have hg : d161207 p = 1 := by simpa only [d161208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13622 p hg
    simpa only [d161208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13624 (p : Pattern) (guard : d161209 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 186 with
  | false =>
    have hg : d161208 p = 1 := by simpa only [d161209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13623 p hg
    simpa only [d161209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13625 (p : Pattern) (guard : d161210 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 185 with
  | false =>
    have hg : d161209 p = 1 := by simpa only [d161210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13624 p hg
    simpa only [d161210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13626 (p : Pattern) (guard : d161211 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 184 with
  | false =>
    have hg : d161210 p = 1 := by simpa only [d161211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13625 p hg
    simpa only [d161211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13627 (p : Pattern) (guard : d161212 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 181 with
  | false =>
    have hg : d161211 p = 1 := by simpa only [d161212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13626 p hg
    simpa only [d161212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13628 (p : Pattern) (guard : d161213 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 177 with
  | false =>
    have hg : d161212 p = 1 := by simpa only [d161213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13627 p hg
    simpa only [d161213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13629 (p : Pattern) (guard : d161214 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 164 with
  | false =>
    have hg : d161213 p = 1 := by simpa only [d161214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13628 p hg
    simpa only [d161214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13630 (p : Pattern) (guard : d161215 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 156 with
  | false =>
    have hg : d161214 p = 1 := by simpa only [d161215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13629 p hg
    simpa only [d161215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13631 (p : Pattern) (guard : d161216 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 155 with
  | false =>
    have hg : d161215 p = 1 := by simpa only [d161216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13630 p hg
    simpa only [d161216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13632 (p : Pattern) (guard : d161217 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 134 with
  | false =>
    have hg : d161216 p = 1 := by simpa only [d161217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13631 p hg
    simpa only [d161217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13633 (p : Pattern) (guard : d161218 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 133 with
  | false =>
    have hg : d161217 p = 1 := by simpa only [d161218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13632 p hg
    simpa only [d161218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13634 (p : Pattern) (guard : d161219 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 120 with
  | false =>
    have hg : d161218 p = 1 := by simpa only [d161219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13633 p hg
    simpa only [d161219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13635 (p : Pattern) (guard : d161220 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 118 with
  | false =>
    have hg : d161219 p = 1 := by simpa only [d161220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13634 p hg
    simpa only [d161220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13636 (p : Pattern) (guard : d161221 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 114 with
  | false =>
    have hg : d161220 p = 1 := by simpa only [d161221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13635 p hg
    simpa only [d161221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13637 (p : Pattern) (guard : d161222 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 111 with
  | false =>
    have hg : d161221 p = 1 := by simpa only [d161222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13636 p hg
    simpa only [d161222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13638 (p : Pattern) (guard : d161223 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 98 with
  | false =>
    have hg : d161222 p = 1 := by simpa only [d161223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13637 p hg
    simpa only [d161223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13639 (p : Pattern) (guard : d161224 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 97 with
  | false =>
    have hg : d161223 p = 1 := by simpa only [d161224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13638 p hg
    simpa only [d161224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13640 (p : Pattern) (guard : d161225 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 94 with
  | false =>
    have hg : d161224 p = 1 := by simpa only [d161225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13639 p hg
    simpa only [d161225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13641 (p : Pattern) (guard : d161226 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 76 with
  | false =>
    have hg : d161225 p = 1 := by simpa only [d161226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13640 p hg
    simpa only [d161226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13642 (p : Pattern) (guard : d161227 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 67 with
  | false =>
    have hg : d161226 p = 1 := by simpa only [d161227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13641 p hg
    simpa only [d161227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13643 (p : Pattern) (guard : d161228 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 52 with
  | false =>
    have hg : d161227 p = 1 := by simpa only [d161228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13642 p hg
    simpa only [d161228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13644 (p : Pattern) (guard : d161229 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 47 with
  | false =>
    have hg : d161228 p = 1 := by simpa only [d161229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13643 p hg
    simpa only [d161229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13645 (p : Pattern) (guard : d161230 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 46 with
  | false =>
    have hg : d161229 p = 1 := by simpa only [d161230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13644 p hg
    simpa only [d161230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13646 (p : Pattern) (guard : d161231 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 45 with
  | false =>
    have hg : d161230 p = 1 := by simpa only [d161231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13645 p hg
    simpa only [d161231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13647 (p : Pattern) (guard : d161232 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 30 with
  | false =>
    have hg : d161231 p = 1 := by simpa only [d161232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13646 p hg
    simpa only [d161232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13648 (p : Pattern) (guard : d161233 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 29 with
  | false =>
    have hg : d161232 p = 1 := by simpa only [d161233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13647 p hg
    simpa only [d161233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13649 (p : Pattern) (guard : d161234 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 28 with
  | false =>
    have hg : d161233 p = 1 := by simpa only [d161234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13648 p hg
    simpa only [d161234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13650 (p : Pattern) (guard : d161235 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 27 with
  | false =>
    have hg : d161234 p = 1 := by simpa only [d161235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13649 p hg
    simpa only [d161235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13651 (p : Pattern) (guard : d161236 p = 1) : d47866 p ≤ (-2 : Int) + d159795 p := by
  cases selected : p 25 with
  | false =>
    have hg : d161235 p = 1 := by simpa only [d161236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13650 p hg
    simpa only [d161236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d161236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare12784 p hg
    simpa only [d161236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13652 (p : Pattern) (guard : d161944 p = 1) : d47866 p ≤ (1 : Int) + d47866 p := by
  omega
theorem compare13653 (p : Pattern) (guard : d162089 p = 1) : d47866 p ≤ (0 : Int) + d47866 p := by
  omega
theorem compare13654 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d48388 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13655 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d48388 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13656 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (1 : Int) + d163714 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13657 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (0 : Int) + d163714 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13658 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d48251 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13659 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d48251 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13660 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d49280 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13661 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d49280 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13662 (p : Pattern) (guard : d0 p = 1) : d48388 p ≤ (-1 : Int) + d48251 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13663 (p : Pattern) (guard : d0 p = 1) : d48388 p ≤ (-2 : Int) + d48251 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13664 (p : Pattern) (guard : d0 p = 1) : d48388 p ≤ (1 : Int) + d171295 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13665 (p : Pattern) (guard : d0 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13666 (p : Pattern) (guard : d0 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13667 (p : Pattern) (guard : d0 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13668 (p : Pattern) (guard : d0 p = 1) : d48336 p ≤ (1 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13669 (p : Pattern) (guard : d0 p = 1) : d48317 p ≤ (1 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13670 (p : Pattern) (guard : d0 p = 1) : d48325 p ≤ (1 : Int) + d48130 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13671 (p : Pattern) (guard : d27 p = 1) : d47664 p ≤ (1 : Int) + d47664 p := by
  omega
theorem compare13672 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d48140 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13673 (p : Pattern) (guard : d28 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13671 p hg
    simpa only [d28, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13672 p hg
    simpa only [d28, d48313, d48141, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13674 (p : Pattern) (guard : d0 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13675 (p : Pattern) (guard : d29 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13673 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13676 (p : Pattern) (guard : d30 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13675 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13677 (p : Pattern) (guard : d31 p = 1) : d48313 p ≤ (1 : Int) + d48141 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13676 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13674 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13678 (p : Pattern) (guard : d32 p = 1) : d48326 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13670 p hg
    simpa only [d32, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31 p = 1 := by simpa only [d32, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13677 p hg
    simpa only [d32, d48326, d48142, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13679 (p : Pattern) (guard : d33 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13669 p hg
    simpa only [d33, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d48337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13678 p hg
    simpa only [d33, d48337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13680 (p : Pattern) (guard : d0 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13681 (p : Pattern) (guard : d34 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13679 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13682 (p : Pattern) (guard : d35 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13681 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13683 (p : Pattern) (guard : d36 p = 1) : d48337 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13682 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13680 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13684 (p : Pattern) (guard : d0 p = 1) : d48328 p ≤ (1 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13685 (p : Pattern) (guard : d37 p = 1) : d48338 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13683 p hg
    simpa only [d37, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d48338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d37, d48338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13686 (p : Pattern) (guard : d38 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13668 p hg
    simpa only [d38, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d48339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13685 p hg
    simpa only [d38, d48339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13687 (p : Pattern) (guard : d39 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13686 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13688 (p : Pattern) (guard : d40 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13687 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13689 (p : Pattern) (guard : d41 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13688 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13690 (p : Pattern) (guard : d42 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d41 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13689 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13691 (p : Pattern) (guard : d43 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d42 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13690 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13692 (p : Pattern) (guard : d44 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d43 p = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13691 p hg
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13693 (p : Pattern) (guard : d45 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d44 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13692 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13694 (p : Pattern) (guard : d46 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13693 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13695 (p : Pattern) (guard : d47 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13694 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13696 (p : Pattern) (guard : d48 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d48, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d48, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d47 p = 1 := by simpa only [d48, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13695 p hg
    simpa only [d48, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13697 (p : Pattern) (guard : d0 p = 1) : d48321 p ≤ (1 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13698 (p : Pattern) (guard : d0 p = 1) : d48324 p ≤ (1 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13699 (p : Pattern) (guard : d33 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13698 p hg
    simpa only [d33, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d48327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13678 p hg
    simpa only [d33, d48327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13700 (p : Pattern) (guard : d0 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13701 (p : Pattern) (guard : d34 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13699 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13702 (p : Pattern) (guard : d35 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13701 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13703 (p : Pattern) (guard : d36 p = 1) : d48327 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13702 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13700 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13704 (p : Pattern) (guard : d37 p = 1) : d48329 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13703 p hg
    simpa only [d37, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d48329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13684 p hg
    simpa only [d37, d48329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13705 (p : Pattern) (guard : d38 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13697 p hg
    simpa only [d38, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d48330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13704 p hg
    simpa only [d38, d48330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13706 (p : Pattern) (guard : d39 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13705 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13707 (p : Pattern) (guard : d40 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13706 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13708 (p : Pattern) (guard : d41 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13707 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13709 (p : Pattern) (guard : d42 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d41 p = 1 := by simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13708 p hg
    simpa only [d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13710 (p : Pattern) (guard : d43 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d42 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13709 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13711 (p : Pattern) (guard : d44 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d43 p = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13710 p hg
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13712 (p : Pattern) (guard : d45 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d44 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13711 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13713 (p : Pattern) (guard : d46 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d45 p = 1 := by simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13712 p hg
    simpa only [d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13714 (p : Pattern) (guard : d47 p = 1) : d48330 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13666 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d46 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13713 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13715 (p : Pattern) (guard : d49 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 93 with
  | false =>
    have hg : d41 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13689 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13716 (p : Pattern) (guard : d50 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 91 with
  | false =>
    have hg : d49 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13715 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13717 (p : Pattern) (guard : d51 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 90 with
  | false =>
    have hg : d50 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13716 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13718 (p : Pattern) (guard : d52 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 89 with
  | false =>
    have hg : d51 p = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13717 p hg
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13719 (p : Pattern) (guard : d53 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d52 p = 1 := by simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13718 p hg
    simpa only [d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13720 (p : Pattern) (guard : d54 p = 1) : d48339 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13667 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53 p = 1 := by simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13719 p hg
    simpa only [d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13721 (p : Pattern) (guard : d55 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 71 with
  | false =>
    have hg : d47 p = 1 := by simpa only [d55, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13714 p hg
    simpa only [d55, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d54 p = 1 := by simpa only [d55, d48340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13720 p hg
    simpa only [d55, d48340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13722 (p : Pattern) (guard : d56 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 70 with
  | false =>
    have hg : d48 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13696 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d55 p = 1 := by simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13721 p hg
    simpa only [d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13723 (p : Pattern) (guard : d57 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 69 with
  | false =>
    have hg : d56 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13722 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13724 (p : Pattern) (guard : d58 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 51 with
  | false =>
    have hg : d57 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13723 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13725 (p : Pattern) (guard : d59 p = 1) : d48340 p ≤ (1 : Int) + d48142 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13665 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d58 p = 1 := by simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13724 p hg
    simpa only [d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13726 (p : Pattern) (guard : d0 p = 1) : d48358 p ≤ (1 : Int) + d171288 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13727 (p : Pattern) (guard : d0 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13728 (p : Pattern) (guard : d0 p = 1) : d48351 p ≤ (1 : Int) + d48178 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13729 (p : Pattern) (guard : d0 p = 1) : d48353 p ≤ (1 : Int) + d48178 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13730 (p : Pattern) (guard : d0 p = 1) : d48344 p ≤ (1 : Int) + d48168 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13731 (p : Pattern) (guard : d27 p = 1) : d47737 p ≤ (1 : Int) + d47737 p := by
  omega
theorem compare13732 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d48176 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13733 (p : Pattern) (guard : d28 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13731 p hg
    simpa only [d28, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13732 p hg
    simpa only [d28, d48345, d48177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13734 (p : Pattern) (guard : d0 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13735 (p : Pattern) (guard : d29 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 159 with
  | false =>
    have hg : d28 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13733 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13736 (p : Pattern) (guard : d30 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 158 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13735 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13737 (p : Pattern) (guard : d31 p = 1) : d48345 p ≤ (1 : Int) + d48177 p := by
  cases selected : p 157 with
  | false =>
    have hg : d30 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13736 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13734 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13738 (p : Pattern) (guard : d32 p = 1) : d48346 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d32, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13730 p hg
    simpa only [d32, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d31 p = 1 := by simpa only [d32, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13737 p hg
    simpa only [d32, d48346, d48178, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13739 (p : Pattern) (guard : d33 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d33, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13729 p hg
    simpa only [d33, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32 p = 1 := by simpa only [d33, d48354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13738 p hg
    simpa only [d33, d48354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13740 (p : Pattern) (guard : d0 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13741 (p : Pattern) (guard : d34 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 136 with
  | false =>
    have hg : d33 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13739 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13742 (p : Pattern) (guard : d35 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 135 with
  | false =>
    have hg : d34 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13741 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13743 (p : Pattern) (guard : d36 p = 1) : d48354 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 119 with
  | false =>
    have hg : d35 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13742 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13740 p hg
    simpa only [d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13744 (p : Pattern) (guard : d0 p = 1) : d48355 p ≤ (1 : Int) + d48178 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare13745 (p : Pattern) (guard : d37 p = 1) : d48356 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 116 with
  | false =>
    have hg : d36 p = 1 := by simpa only [d37, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13743 p hg
    simpa only [d37, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d37, d48356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13744 p hg
    simpa only [d37, d48356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13746 (p : Pattern) (guard : d38 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13728 p hg
    simpa only [d38, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d37 p = 1 := by simpa only [d38, d48357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13745 p hg
    simpa only [d38, d48357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13747 (p : Pattern) (guard : d39 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 113 with
  | false =>
    have hg : d38 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13746 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13748 (p : Pattern) (guard : d40 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 96 with
  | false =>
    have hg : d39 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13747 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare13749 (p : Pattern) (guard : d41 p = 1) : d48357 p ≤ (1 : Int) + d48178 p := by
  cases selected : p 95 with
  | false =>
    have hg : d40 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13748 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare13727 p hg
    simpa only [d41, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
