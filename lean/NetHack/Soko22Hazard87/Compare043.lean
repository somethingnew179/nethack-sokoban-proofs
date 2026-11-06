import NetHack.Soko22Hazard87.Compare042
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare10750 (p : Pattern) (guard : d9633 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9627 p = 1 := by simpa only [d9633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10748 p hg
    simpa only [d9633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9632 p = 1 := by simpa only [d9633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10749 p hg
    simpa only [d9633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10751 (p : Pattern) (guard : d9634 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d9634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9633 p = 1 := by simpa only [d9634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10750 p hg
    simpa only [d9634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10752 (p : Pattern) (guard : d9635 p = 1) : d48276 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9634 p = 1 := by simpa only [d9635, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10751 p hg
    simpa only [d9635, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9635, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10647 p hg
    simpa only [d9635, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10753 (p : Pattern) (guard : d9636 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9636, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10637 p hg
    simpa only [d9636, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9635 p = 1 := by simpa only [d9636, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10752 p hg
    simpa only [d9636, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10754 (p : Pattern) (guard : d9641 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9632 p = 1 := by simpa only [d9641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10749 p hg
    simpa only [d9641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d9641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10755 (p : Pattern) (guard : d9642 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d9642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9641 p = 1 := by simpa only [d9642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10754 p hg
    simpa only [d9642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10756 (p : Pattern) (guard : d9643 p = 1) : d48276 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9642 p = 1 := by simpa only [d9643, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10755 p hg
    simpa only [d9643, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9643, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10647 p hg
    simpa only [d9643, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10757 (p : Pattern) (guard : d9644 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9644, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10637 p hg
    simpa only [d9644, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9643 p = 1 := by simpa only [d9644, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10756 p hg
    simpa only [d9644, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10758 (p : Pattern) (guard : d9645 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9636 p = 1 := by simpa only [d9645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10753 p hg
    simpa only [d9645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9644 p = 1 := by simpa only [d9645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10757 p hg
    simpa only [d9645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10759 (p : Pattern) (guard : d9646 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9645 p = 1 := by simpa only [d9646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10758 p hg
    simpa only [d9646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10760 (p : Pattern) (guard : d9647 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9646 p = 1 := by simpa only [d9647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10759 p hg
    simpa only [d9647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10761 (p : Pattern) (guard : d9648 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9647 p = 1 := by simpa only [d9648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10760 p hg
    simpa only [d9648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10762 (p : Pattern) (guard : d9722 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9644 p = 1 := by simpa only [d9722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10757 p hg
    simpa only [d9722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10763 (p : Pattern) (guard : d9723 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d9722 p = 1 := by simpa only [d9723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10762 p hg
    simpa only [d9723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10764 (p : Pattern) (guard : d9724 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d9723 p = 1 := by simpa only [d9724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10763 p hg
    simpa only [d9724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10765 (p : Pattern) (guard : d9725 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d9724 p = 1 := by simpa only [d9725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10764 p hg
    simpa only [d9725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d9725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10766 (p : Pattern) (guard : d129519 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d9648 p = 1 := by simpa only [d129519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10761 p hg
    simpa only [d129519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9725 p = 1 := by simpa only [d129519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10765 p hg
    simpa only [d129519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10767 (p : Pattern) (guard : d129520 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129519 p = 1 := by simpa only [d129520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10766 p hg
    simpa only [d129520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10768 (p : Pattern) (guard : d129521 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d129520 p = 1 := by simpa only [d129521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10767 p hg
    simpa only [d129521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10769 (p : Pattern) (guard : d129522 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129521 p = 1 := by simpa only [d129522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10768 p hg
    simpa only [d129522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10770 (p : Pattern) (guard : d129523 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129522 p = 1 := by simpa only [d129523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10769 p hg
    simpa only [d129523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10771 (p : Pattern) (guard : d129524 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129524, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10635 p hg
    simpa only [d129524, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129523 p = 1 := by simpa only [d129524, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10770 p hg
    simpa only [d129524, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10772 (p : Pattern) (guard : d129525 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129524 p = 1 := by simpa only [d129525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10771 p hg
    simpa only [d129525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10773 (p : Pattern) (guard : d129526 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d129525 p = 1 := by simpa only [d129526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10772 p hg
    simpa only [d129526, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129526, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129526, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10774 (p : Pattern) (guard : d129527 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d129526 p = 1 := by simpa only [d129527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10773 p hg
    simpa only [d129527, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129527, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129527, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10775 (p : Pattern) (guard : d129528 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d129527 p = 1 := by simpa only [d129528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10774 p hg
    simpa only [d129528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10776 (p : Pattern) (guard : d129529 p = 1) : d48307 p ≤ (0 : Int) + d47910 p := by
  cases selected : p 49 with
  | false =>
    have hg : d129528 p = 1 := by simpa only [d129529, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10775 p hg
    simpa only [d129529, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129529, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10664 p hg
    simpa only [d129529, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10777 (p : Pattern) (guard : d129530 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129530, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10633 p hg
    simpa only [d129530, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129529 p = 1 := by simpa only [d129530, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10776 p hg
    simpa only [d129530, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10778 (p : Pattern) (guard : d129531 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129530 p = 1 := by simpa only [d129531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10777 p hg
    simpa only [d129531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10779 (p : Pattern) (guard : d129532 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129531 p = 1 := by simpa only [d129532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10778 p hg
    simpa only [d129532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10780 (p : Pattern) (guard : d129533 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129532 p = 1 := by simpa only [d129533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10779 p hg
    simpa only [d129533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10781 (p : Pattern) (guard : d129534 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129533 p = 1 := by simpa only [d129534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10780 p hg
    simpa only [d129534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10782 (p : Pattern) (guard : d129535 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129534 p = 1 := by simpa only [d129535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10781 p hg
    simpa only [d129535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10783 (p : Pattern) (guard : d129536 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129535 p = 1 := by simpa only [d129536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10782 p hg
    simpa only [d129536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10784 (p : Pattern) (guard : d129537 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129536 p = 1 := by simpa only [d129537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10783 p hg
    simpa only [d129537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10785 (p : Pattern) (guard : d129538 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d129518 p = 1 := by simpa only [d129538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10741 p hg
    simpa only [d129538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129537 p = 1 := by simpa only [d129538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10784 p hg
    simpa only [d129538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10786 (p : Pattern) (guard : d9834 p = 1) : d47681 p ≤ (0 : Int) + d47681 p := by
  omega
theorem compare10787 (p : Pattern) (guard : d9835 p = 1) : d48273 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9834 p = 1 := by simpa only [d9835, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10786 p hg
    simpa only [d9835, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9835, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10641 p hg
    simpa only [d9835, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10788 (p : Pattern) (guard : d9836 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9836, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10639 p hg
    simpa only [d9836, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9835 p = 1 := by simpa only [d9836, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10787 p hg
    simpa only [d9836, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10789 (p : Pattern) (guard : d9851 p = 1) : d47681 p ≤ (0 : Int) + d47681 p := by
  omega
theorem compare10790 (p : Pattern) (guard : d9852 p = 1) : d48273 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9851 p = 1 := by simpa only [d9852, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10789 p hg
    simpa only [d9852, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9852, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10641 p hg
    simpa only [d9852, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10791 (p : Pattern) (guard : d9853 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9853, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10639 p hg
    simpa only [d9853, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9852 p = 1 := by simpa only [d9853, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10790 p hg
    simpa only [d9853, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10792 (p : Pattern) (guard : d9854 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9836 p = 1 := by simpa only [d9854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10788 p hg
    simpa only [d9854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9853 p = 1 := by simpa only [d9854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10791 p hg
    simpa only [d9854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10793 (p : Pattern) (guard : d9870 p = 1) : d47681 p ≤ (0 : Int) + d47681 p := by
  omega
theorem compare10794 (p : Pattern) (guard : d9871 p = 1) : d48273 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d9870 p = 1 := by simpa only [d9871, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10793 p hg
    simpa only [d9871, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9871, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10641 p hg
    simpa only [d9871, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10795 (p : Pattern) (guard : d9872 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9872, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10639 p hg
    simpa only [d9872, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9871 p = 1 := by simpa only [d9872, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10794 p hg
    simpa only [d9872, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10796 (p : Pattern) (guard : d9873 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d9872 p = 1 := by simpa only [d9873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10795 p hg
    simpa only [d9873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d9873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10797 (p : Pattern) (guard : d129539 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9854 p = 1 := by simpa only [d129539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10792 p hg
    simpa only [d129539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9873 p = 1 := by simpa only [d129539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10796 p hg
    simpa only [d129539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10798 (p : Pattern) (guard : d129540 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d129540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129539 p = 1 := by simpa only [d129540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10797 p hg
    simpa only [d129540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10799 (p : Pattern) (guard : d129541 p = 1) : d48276 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d129540 p = 1 := by simpa only [d129541, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10798 p hg
    simpa only [d129541, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129541, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10647 p hg
    simpa only [d129541, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10800 (p : Pattern) (guard : d129542 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129542, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10637 p hg
    simpa only [d129542, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129541 p = 1 := by simpa only [d129542, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10799 p hg
    simpa only [d129542, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10801 (p : Pattern) (guard : d9874 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d9873 p = 1 := by simpa only [d9874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10796 p hg
    simpa only [d9874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d9874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10802 (p : Pattern) (guard : d9875 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d9875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9874 p = 1 := by simpa only [d9875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10801 p hg
    simpa only [d9875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10803 (p : Pattern) (guard : d9876 p = 1) : d48276 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d9875 p = 1 := by simpa only [d9876, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10802 p hg
    simpa only [d9876, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d9876, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10647 p hg
    simpa only [d9876, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10804 (p : Pattern) (guard : d9877 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d9877, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10637 p hg
    simpa only [d9877, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9876 p = 1 := by simpa only [d9877, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10803 p hg
    simpa only [d9877, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10805 (p : Pattern) (guard : d129543 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d129542 p = 1 := by simpa only [d129543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10800 p hg
    simpa only [d129543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d9877 p = 1 := by simpa only [d129543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10804 p hg
    simpa only [d129543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10806 (p : Pattern) (guard : d129544 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d129543 p = 1 := by simpa only [d129544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10805 p hg
    simpa only [d129544, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129544, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129544, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10807 (p : Pattern) (guard : d129545 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d129544 p = 1 := by simpa only [d129545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10806 p hg
    simpa only [d129545, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129545, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129545, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10808 (p : Pattern) (guard : d129546 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d129545 p = 1 := by simpa only [d129546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10807 p hg
    simpa only [d129546, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129546, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129546, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10809 (p : Pattern) (guard : d10007 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d9877 p = 1 := by simpa only [d10007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10804 p hg
    simpa only [d10007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d10007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10810 (p : Pattern) (guard : d10008 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d10007 p = 1 := by simpa only [d10008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10809 p hg
    simpa only [d10008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d10008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10811 (p : Pattern) (guard : d10009 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d10008 p = 1 := by simpa only [d10009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10810 p hg
    simpa only [d10009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d10009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10812 (p : Pattern) (guard : d10010 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d10009 p = 1 := by simpa only [d10010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10811 p hg
    simpa only [d10010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d10010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10813 (p : Pattern) (guard : d129547 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d129546 p = 1 := by simpa only [d129547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10808 p hg
    simpa only [d129547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10010 p = 1 := by simpa only [d129547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10812 p hg
    simpa only [d129547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10814 (p : Pattern) (guard : d129548 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129547 p = 1 := by simpa only [d129548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10813 p hg
    simpa only [d129548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10815 (p : Pattern) (guard : d129549 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d129548 p = 1 := by simpa only [d129549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10814 p hg
    simpa only [d129549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10816 (p : Pattern) (guard : d129550 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129550, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129549 p = 1 := by simpa only [d129550, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10815 p hg
    simpa only [d129550, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10817 (p : Pattern) (guard : d129551 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129550 p = 1 := by simpa only [d129551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10816 p hg
    simpa only [d129551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10818 (p : Pattern) (guard : d129552 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129552, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10635 p hg
    simpa only [d129552, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129551 p = 1 := by simpa only [d129552, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10817 p hg
    simpa only [d129552, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10819 (p : Pattern) (guard : d129553 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129552 p = 1 := by simpa only [d129553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10818 p hg
    simpa only [d129553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10820 (p : Pattern) (guard : d129554 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d129553 p = 1 := by simpa only [d129554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10819 p hg
    simpa only [d129554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10821 (p : Pattern) (guard : d129555 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d129554 p = 1 := by simpa only [d129555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10820 p hg
    simpa only [d129555, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129555, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129555, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10822 (p : Pattern) (guard : d129556 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d129555 p = 1 := by simpa only [d129556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10821 p hg
    simpa only [d129556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10823 (p : Pattern) (guard : d129557 p = 1) : d48307 p ≤ (0 : Int) + d47910 p := by
  cases selected : p 49 with
  | false =>
    have hg : d129556 p = 1 := by simpa only [d129557, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10822 p hg
    simpa only [d129557, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129557, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10664 p hg
    simpa only [d129557, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10824 (p : Pattern) (guard : d129558 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129558, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10633 p hg
    simpa only [d129558, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129557 p = 1 := by simpa only [d129558, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10823 p hg
    simpa only [d129558, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10825 (p : Pattern) (guard : d129559 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129559, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129558 p = 1 := by simpa only [d129559, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10824 p hg
    simpa only [d129559, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10826 (p : Pattern) (guard : d129560 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129559 p = 1 := by simpa only [d129560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10825 p hg
    simpa only [d129560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10827 (p : Pattern) (guard : d129561 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129560 p = 1 := by simpa only [d129561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10826 p hg
    simpa only [d129561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10828 (p : Pattern) (guard : d129562 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129561 p = 1 := by simpa only [d129562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10827 p hg
    simpa only [d129562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10829 (p : Pattern) (guard : d129563 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129563, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129562 p = 1 := by simpa only [d129563, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10828 p hg
    simpa only [d129563, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10830 (p : Pattern) (guard : d129564 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129564, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129563 p = 1 := by simpa only [d129564, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10829 p hg
    simpa only [d129564, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10831 (p : Pattern) (guard : d129565 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129565, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129564 p = 1 := by simpa only [d129565, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10830 p hg
    simpa only [d129565, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10832 (p : Pattern) (guard : d129566 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129566, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129565 p = 1 := by simpa only [d129566, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10831 p hg
    simpa only [d129566, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10833 (p : Pattern) (guard : d129567 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d129538 p = 1 := by simpa only [d129567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10785 p hg
    simpa only [d129567, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129566 p = 1 := by simpa only [d129567, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10832 p hg
    simpa only [d129567, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10834 (p : Pattern) (guard : d10122 p = 1) : d47681 p ≤ (0 : Int) + d47681 p := by
  omega
theorem compare10835 (p : Pattern) (guard : d10123 p = 1) : d48273 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10122 p = 1 := by simpa only [d10123, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10834 p hg
    simpa only [d10123, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10123, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10641 p hg
    simpa only [d10123, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10836 (p : Pattern) (guard : d10124 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10124, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10639 p hg
    simpa only [d10124, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10123 p = 1 := by simpa only [d10124, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10835 p hg
    simpa only [d10124, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10837 (p : Pattern) (guard : d10142 p = 1) : d47681 p ≤ (0 : Int) + d47681 p := by
  omega
theorem compare10838 (p : Pattern) (guard : d10143 p = 1) : d48273 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10142 p = 1 := by simpa only [d10143, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10837 p hg
    simpa only [d10143, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10143, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10641 p hg
    simpa only [d10143, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10839 (p : Pattern) (guard : d10144 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10144, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10639 p hg
    simpa only [d10144, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10143 p = 1 := by simpa only [d10144, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10838 p hg
    simpa only [d10144, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10840 (p : Pattern) (guard : d10145 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d10124 p = 1 := by simpa only [d10145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10836 p hg
    simpa only [d10145, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10144 p = 1 := by simpa only [d10145, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10839 p hg
    simpa only [d10145, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10841 (p : Pattern) (guard : d10164 p = 1) : d47681 p ≤ (0 : Int) + d47681 p := by
  omega
theorem compare10842 (p : Pattern) (guard : d10165 p = 1) : d48273 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10164 p = 1 := by simpa only [d10165, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10841 p hg
    simpa only [d10165, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10165, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10641 p hg
    simpa only [d10165, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10843 (p : Pattern) (guard : d10166 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10166, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10639 p hg
    simpa only [d10166, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10165 p = 1 := by simpa only [d10166, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10842 p hg
    simpa only [d10166, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10844 (p : Pattern) (guard : d10167 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d10166 p = 1 := by simpa only [d10167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10843 p hg
    simpa only [d10167, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10167, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d10167, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10845 (p : Pattern) (guard : d129568 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d10145 p = 1 := by simpa only [d129568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10840 p hg
    simpa only [d129568, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10167 p = 1 := by simpa only [d129568, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10844 p hg
    simpa only [d129568, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10846 (p : Pattern) (guard : d129569 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d129569, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129568 p = 1 := by simpa only [d129569, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10845 p hg
    simpa only [d129569, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10847 (p : Pattern) (guard : d129570 p = 1) : d48276 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d129569 p = 1 := by simpa only [d129570, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10846 p hg
    simpa only [d129570, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129570, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10647 p hg
    simpa only [d129570, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10848 (p : Pattern) (guard : d129571 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129571, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10637 p hg
    simpa only [d129571, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129570 p = 1 := by simpa only [d129571, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10847 p hg
    simpa only [d129571, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10849 (p : Pattern) (guard : d10168 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d10167 p = 1 := by simpa only [d10168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10844 p hg
    simpa only [d10168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d10168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10850 (p : Pattern) (guard : d10169 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d10169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10168 p = 1 := by simpa only [d10169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10849 p hg
    simpa only [d10169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10851 (p : Pattern) (guard : d10170 p = 1) : d48276 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d10169 p = 1 := by simpa only [d10170, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10850 p hg
    simpa only [d10170, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10170, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10647 p hg
    simpa only [d10170, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10852 (p : Pattern) (guard : d10171 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10171, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10637 p hg
    simpa only [d10171, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10170 p = 1 := by simpa only [d10171, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10851 p hg
    simpa only [d10171, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10853 (p : Pattern) (guard : d129572 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d129571 p = 1 := by simpa only [d129572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10848 p hg
    simpa only [d129572, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10171 p = 1 := by simpa only [d129572, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10852 p hg
    simpa only [d129572, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10854 (p : Pattern) (guard : d129573 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d129572 p = 1 := by simpa only [d129573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10853 p hg
    simpa only [d129573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10855 (p : Pattern) (guard : d129574 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d129573 p = 1 := by simpa only [d129574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10854 p hg
    simpa only [d129574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10856 (p : Pattern) (guard : d129575 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d129574 p = 1 := by simpa only [d129575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10855 p hg
    simpa only [d129575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10857 (p : Pattern) (guard : d10313 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d10171 p = 1 := by simpa only [d10313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10852 p hg
    simpa only [d10313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d10313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10858 (p : Pattern) (guard : d10314 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d10313 p = 1 := by simpa only [d10314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10857 p hg
    simpa only [d10314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d10314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10859 (p : Pattern) (guard : d10315 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d10314 p = 1 := by simpa only [d10315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10858 p hg
    simpa only [d10315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d10315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10860 (p : Pattern) (guard : d10316 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d10315 p = 1 := by simpa only [d10316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10859 p hg
    simpa only [d10316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d10316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10861 (p : Pattern) (guard : d129576 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d129575 p = 1 := by simpa only [d129576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10856 p hg
    simpa only [d129576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10316 p = 1 := by simpa only [d129576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10860 p hg
    simpa only [d129576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10862 (p : Pattern) (guard : d129577 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129576 p = 1 := by simpa only [d129577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10861 p hg
    simpa only [d129577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10863 (p : Pattern) (guard : d129578 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d129577 p = 1 := by simpa only [d129578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10862 p hg
    simpa only [d129578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10864 (p : Pattern) (guard : d129579 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129578 p = 1 := by simpa only [d129579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10863 p hg
    simpa only [d129579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10865 (p : Pattern) (guard : d129580 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129579 p = 1 := by simpa only [d129580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10864 p hg
    simpa only [d129580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10866 (p : Pattern) (guard : d129581 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129581, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10635 p hg
    simpa only [d129581, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129580 p = 1 := by simpa only [d129581, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10865 p hg
    simpa only [d129581, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10867 (p : Pattern) (guard : d129582 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129581 p = 1 := by simpa only [d129582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10866 p hg
    simpa only [d129582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10868 (p : Pattern) (guard : d129583 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d129582 p = 1 := by simpa only [d129583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10867 p hg
    simpa only [d129583, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129583, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129583, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10869 (p : Pattern) (guard : d129584 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d129583 p = 1 := by simpa only [d129584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10868 p hg
    simpa only [d129584, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129584, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129584, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10870 (p : Pattern) (guard : d129585 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d129584 p = 1 := by simpa only [d129585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10869 p hg
    simpa only [d129585, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129585, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129585, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10871 (p : Pattern) (guard : d129586 p = 1) : d48307 p ≤ (0 : Int) + d47910 p := by
  cases selected : p 49 with
  | false =>
    have hg : d129585 p = 1 := by simpa only [d129586, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10870 p hg
    simpa only [d129586, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129586, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10664 p hg
    simpa only [d129586, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10872 (p : Pattern) (guard : d129587 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129587, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10633 p hg
    simpa only [d129587, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129586 p = 1 := by simpa only [d129587, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10871 p hg
    simpa only [d129587, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10873 (p : Pattern) (guard : d129588 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129587 p = 1 := by simpa only [d129588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10872 p hg
    simpa only [d129588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10874 (p : Pattern) (guard : d129589 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129588 p = 1 := by simpa only [d129589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10873 p hg
    simpa only [d129589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10875 (p : Pattern) (guard : d129590 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129590, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129589 p = 1 := by simpa only [d129590, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10874 p hg
    simpa only [d129590, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10876 (p : Pattern) (guard : d129591 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129590 p = 1 := by simpa only [d129591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10875 p hg
    simpa only [d129591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10877 (p : Pattern) (guard : d129592 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129591 p = 1 := by simpa only [d129592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10876 p hg
    simpa only [d129592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10878 (p : Pattern) (guard : d129593 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129592 p = 1 := by simpa only [d129593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10877 p hg
    simpa only [d129593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10879 (p : Pattern) (guard : d129594 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129593 p = 1 := by simpa only [d129594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10878 p hg
    simpa only [d129594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10880 (p : Pattern) (guard : d129595 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129595, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129594 p = 1 := by simpa only [d129595, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10879 p hg
    simpa only [d129595, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10881 (p : Pattern) (guard : d129596 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129595 p = 1 := by simpa only [d129596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10880 p hg
    simpa only [d129596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10882 (p : Pattern) (guard : d129597 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d129567 p = 1 := by simpa only [d129597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10833 p hg
    simpa only [d129597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129596 p = 1 := by simpa only [d129597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10881 p hg
    simpa only [d129597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10883 (p : Pattern) (guard : d10398 p = 1) : d47681 p ≤ (0 : Int) + d47681 p := by
  omega
theorem compare10884 (p : Pattern) (guard : d10399 p = 1) : d48273 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10398 p = 1 := by simpa only [d10399, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10883 p hg
    simpa only [d10399, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10399, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10641 p hg
    simpa only [d10399, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10885 (p : Pattern) (guard : d10400 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10400, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10639 p hg
    simpa only [d10400, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10399 p = 1 := by simpa only [d10400, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10884 p hg
    simpa only [d10400, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10886 (p : Pattern) (guard : d10419 p = 1) : d47681 p ≤ (0 : Int) + d47681 p := by
  omega
theorem compare10887 (p : Pattern) (guard : d10420 p = 1) : d48273 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10419 p = 1 := by simpa only [d10420, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10886 p hg
    simpa only [d10420, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10420, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10641 p hg
    simpa only [d10420, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10888 (p : Pattern) (guard : d10421 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10421, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10639 p hg
    simpa only [d10421, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10420 p = 1 := by simpa only [d10421, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10887 p hg
    simpa only [d10421, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10889 (p : Pattern) (guard : d10422 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d10400 p = 1 := by simpa only [d10422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10885 p hg
    simpa only [d10422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10421 p = 1 := by simpa only [d10422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10888 p hg
    simpa only [d10422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10890 (p : Pattern) (guard : d10441 p = 1) : d47681 p ≤ (0 : Int) + d47681 p := by
  omega
theorem compare10891 (p : Pattern) (guard : d10442 p = 1) : d48273 p ≤ (0 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d10441 p = 1 := by simpa only [d10442, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10890 p hg
    simpa only [d10442, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10442, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10641 p hg
    simpa only [d10442, d48273, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10892 (p : Pattern) (guard : d10443 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10443, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10639 p hg
    simpa only [d10443, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10442 p = 1 := by simpa only [d10443, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10891 p hg
    simpa only [d10443, d48274, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10893 (p : Pattern) (guard : d10444 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d10443 p = 1 := by simpa only [d10444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10892 p hg
    simpa only [d10444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d10444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10894 (p : Pattern) (guard : d129598 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d10422 p = 1 := by simpa only [d129598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10889 p hg
    simpa only [d129598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10444 p = 1 := by simpa only [d129598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10893 p hg
    simpa only [d129598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10895 (p : Pattern) (guard : d129599 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d129599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129598 p = 1 := by simpa only [d129599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10894 p hg
    simpa only [d129599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10896 (p : Pattern) (guard : d129600 p = 1) : d48276 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d129599 p = 1 := by simpa only [d129600, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10895 p hg
    simpa only [d129600, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129600, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10647 p hg
    simpa only [d129600, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10897 (p : Pattern) (guard : d129601 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129601, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10637 p hg
    simpa only [d129601, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129600 p = 1 := by simpa only [d129601, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10896 p hg
    simpa only [d129601, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10898 (p : Pattern) (guard : d10445 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 135 with
  | false =>
    have hg : d10444 p = 1 := by simpa only [d10445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10893 p hg
    simpa only [d10445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d10445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10899 (p : Pattern) (guard : d10446 p = 1) : d48274 p ≤ (0 : Int) + d47687 p := by
  cases selected : p 119 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10638 p hg
    simpa only [d10446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10445 p = 1 := by simpa only [d10446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10898 p hg
    simpa only [d10446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10900 (p : Pattern) (guard : d10447 p = 1) : d48276 p ≤ (0 : Int) + d47699 p := by
  cases selected : p 116 with
  | false =>
    have hg : d10446 p = 1 := by simpa only [d10447, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10899 p hg
    simpa only [d10447, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10447, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10647 p hg
    simpa only [d10447, d48276, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10901 (p : Pattern) (guard : d10448 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d10448, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10637 p hg
    simpa only [d10448, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10447 p = 1 := by simpa only [d10448, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10900 p hg
    simpa only [d10448, d48277, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10902 (p : Pattern) (guard : d129602 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d129601 p = 1 := by simpa only [d129602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10897 p hg
    simpa only [d129602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10448 p = 1 := by simpa only [d129602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10901 p hg
    simpa only [d129602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10903 (p : Pattern) (guard : d129603 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d129602 p = 1 := by simpa only [d129603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10902 p hg
    simpa only [d129603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10904 (p : Pattern) (guard : d129604 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d129603 p = 1 := by simpa only [d129604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10903 p hg
    simpa only [d129604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10905 (p : Pattern) (guard : d129605 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d129604 p = 1 := by simpa only [d129605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10904 p hg
    simpa only [d129605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10906 (p : Pattern) (guard : d10579 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 113 with
  | false =>
    have hg : d10448 p = 1 := by simpa only [d10579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10901 p hg
    simpa only [d10579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d10579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10907 (p : Pattern) (guard : d10580 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 96 with
  | false =>
    have hg : d10579 p = 1 := by simpa only [d10580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10906 p hg
    simpa only [d10580, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10580, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d10580, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10908 (p : Pattern) (guard : d10581 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 95 with
  | false =>
    have hg : d10580 p = 1 := by simpa only [d10581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10907 p hg
    simpa only [d10581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d10581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10909 (p : Pattern) (guard : d10582 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 93 with
  | false =>
    have hg : d10581 p = 1 := by simpa only [d10582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10908 p hg
    simpa only [d10582, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d10582, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d10582, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10910 (p : Pattern) (guard : d129606 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 91 with
  | false =>
    have hg : d129605 p = 1 := by simpa only [d129606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10905 p hg
    simpa only [d129606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10582 p = 1 := by simpa only [d129606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10909 p hg
    simpa only [d129606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10911 (p : Pattern) (guard : d129607 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129606 p = 1 := by simpa only [d129607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10910 p hg
    simpa only [d129607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10912 (p : Pattern) (guard : d129608 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 89 with
  | false =>
    have hg : d129607 p = 1 := by simpa only [d129608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10911 p hg
    simpa only [d129608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10913 (p : Pattern) (guard : d129609 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129608 p = 1 := by simpa only [d129609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10912 p hg
    simpa only [d129609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10914 (p : Pattern) (guard : d129610 p = 1) : d48277 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10636 p hg
    simpa only [d129610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129609 p = 1 := by simpa only [d129610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10913 p hg
    simpa only [d129610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10915 (p : Pattern) (guard : d129611 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129611, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10635 p hg
    simpa only [d129611, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129610 p = 1 := by simpa only [d129611, d48278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10914 p hg
    simpa only [d129611, d48278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10916 (p : Pattern) (guard : d129612 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129611 p = 1 := by simpa only [d129612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10915 p hg
    simpa only [d129612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10917 (p : Pattern) (guard : d129613 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 69 with
  | false =>
    have hg : d129612 p = 1 := by simpa only [d129613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10916 p hg
    simpa only [d129613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10918 (p : Pattern) (guard : d129614 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 51 with
  | false =>
    have hg : d129613 p = 1 := by simpa only [d129614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10917 p hg
    simpa only [d129614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10919 (p : Pattern) (guard : d129615 p = 1) : d48278 p ≤ (0 : Int) + d47700 p := by
  cases selected : p 50 with
  | false =>
    have hg : d129614 p = 1 := by simpa only [d129615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10918 p hg
    simpa only [d129615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10634 p hg
    simpa only [d129615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10920 (p : Pattern) (guard : d129616 p = 1) : d48307 p ≤ (0 : Int) + d47910 p := by
  cases selected : p 49 with
  | false =>
    have hg : d129615 p = 1 := by simpa only [d129616, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10919 p hg
    simpa only [d129616, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129616, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10664 p hg
    simpa only [d129616, d48307, d47910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10921 (p : Pattern) (guard : d129617 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129617, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10633 p hg
    simpa only [d129617, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129616 p = 1 := by simpa only [d129617, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10920 p hg
    simpa only [d129617, d48308, d47911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10922 (p : Pattern) (guard : d129618 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129617 p = 1 := by simpa only [d129618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10921 p hg
    simpa only [d129618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10923 (p : Pattern) (guard : d129619 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129618 p = 1 := by simpa only [d129619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10922 p hg
    simpa only [d129619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10924 (p : Pattern) (guard : d129620 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129619 p = 1 := by simpa only [d129620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10923 p hg
    simpa only [d129620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10925 (p : Pattern) (guard : d129621 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129620 p = 1 := by simpa only [d129621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10924 p hg
    simpa only [d129621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10926 (p : Pattern) (guard : d129622 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129621 p = 1 := by simpa only [d129622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10925 p hg
    simpa only [d129622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10927 (p : Pattern) (guard : d129623 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129622 p = 1 := by simpa only [d129623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10926 p hg
    simpa only [d129623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10928 (p : Pattern) (guard : d129624 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129623 p = 1 := by simpa only [d129624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10927 p hg
    simpa only [d129624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10929 (p : Pattern) (guard : d129625 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129624 p = 1 := by simpa only [d129625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10928 p hg
    simpa only [d129625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10930 (p : Pattern) (guard : d129626 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129625 p = 1 := by simpa only [d129626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10929 p hg
    simpa only [d129626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10931 (p : Pattern) (guard : d129627 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d129627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129626 p = 1 := by simpa only [d129627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10930 p hg
    simpa only [d129627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10932 (p : Pattern) (guard : d129628 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d129597 p = 1 := by simpa only [d129628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10882 p hg
    simpa only [d129628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d129627 p = 1 := by simpa only [d129628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10931 p hg
    simpa only [d129628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10933 (p : Pattern) (guard : d129629 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 260 with
  | false =>
    have hg : d129628 p = 1 := by simpa only [d129629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10932 p hg
    simpa only [d129629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10934 (p : Pattern) (guard : d129630 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 259 with
  | false =>
    have hg : d129629 p = 1 := by simpa only [d129630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10933 p hg
    simpa only [d129630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10935 (p : Pattern) (guard : d129631 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 258 with
  | false =>
    have hg : d129630 p = 1 := by simpa only [d129631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10934 p hg
    simpa only [d129631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10936 (p : Pattern) (guard : d129632 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 257 with
  | false =>
    have hg : d129631 p = 1 := by simpa only [d129632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10935 p hg
    simpa only [d129632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10937 (p : Pattern) (guard : d129633 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 256 with
  | false =>
    have hg : d129632 p = 1 := by simpa only [d129633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10936 p hg
    simpa only [d129633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10938 (p : Pattern) (guard : d129634 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 255 with
  | false =>
    have hg : d129633 p = 1 := by simpa only [d129634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10937 p hg
    simpa only [d129634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10939 (p : Pattern) (guard : d129635 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 254 with
  | false =>
    have hg : d129634 p = 1 := by simpa only [d129635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10938 p hg
    simpa only [d129635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10940 (p : Pattern) (guard : d129636 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 253 with
  | false =>
    have hg : d129635 p = 1 := by simpa only [d129636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10939 p hg
    simpa only [d129636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10941 (p : Pattern) (guard : d129637 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 252 with
  | false =>
    have hg : d129636 p = 1 := by simpa only [d129637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10940 p hg
    simpa only [d129637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10942 (p : Pattern) (guard : d129638 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 251 with
  | false =>
    have hg : d129637 p = 1 := by simpa only [d129638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10941 p hg
    simpa only [d129638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10943 (p : Pattern) (guard : d129639 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 250 with
  | false =>
    have hg : d129638 p = 1 := by simpa only [d129639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10942 p hg
    simpa only [d129639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10944 (p : Pattern) (guard : d129640 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 249 with
  | false =>
    have hg : d129639 p = 1 := by simpa only [d129640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10943 p hg
    simpa only [d129640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10945 (p : Pattern) (guard : d129641 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 245 with
  | false =>
    have hg : d129640 p = 1 := by simpa only [d129641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10944 p hg
    simpa only [d129641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10946 (p : Pattern) (guard : d129642 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 200 with
  | false =>
    have hg : d129641 p = 1 := by simpa only [d129642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10945 p hg
    simpa only [d129642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10947 (p : Pattern) (guard : d129643 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 199 with
  | false =>
    have hg : d129642 p = 1 := by simpa only [d129643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10946 p hg
    simpa only [d129643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10948 (p : Pattern) (guard : d129644 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 186 with
  | false =>
    have hg : d129643 p = 1 := by simpa only [d129644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10947 p hg
    simpa only [d129644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10949 (p : Pattern) (guard : d129645 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 185 with
  | false =>
    have hg : d129644 p = 1 := by simpa only [d129645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10948 p hg
    simpa only [d129645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10950 (p : Pattern) (guard : d129646 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 184 with
  | false =>
    have hg : d129645 p = 1 := by simpa only [d129646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10949 p hg
    simpa only [d129646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10951 (p : Pattern) (guard : d129647 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 181 with
  | false =>
    have hg : d129646 p = 1 := by simpa only [d129647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10950 p hg
    simpa only [d129647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10952 (p : Pattern) (guard : d129648 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 177 with
  | false =>
    have hg : d129647 p = 1 := by simpa only [d129648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10951 p hg
    simpa only [d129648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10953 (p : Pattern) (guard : d129649 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 164 with
  | false =>
    have hg : d129648 p = 1 := by simpa only [d129649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10952 p hg
    simpa only [d129649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10954 (p : Pattern) (guard : d129650 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 156 with
  | false =>
    have hg : d129649 p = 1 := by simpa only [d129650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10953 p hg
    simpa only [d129650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10955 (p : Pattern) (guard : d129651 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 155 with
  | false =>
    have hg : d129650 p = 1 := by simpa only [d129651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10954 p hg
    simpa only [d129651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10956 (p : Pattern) (guard : d129652 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 134 with
  | false =>
    have hg : d129651 p = 1 := by simpa only [d129652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10955 p hg
    simpa only [d129652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10957 (p : Pattern) (guard : d129653 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 133 with
  | false =>
    have hg : d129652 p = 1 := by simpa only [d129653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10956 p hg
    simpa only [d129653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10958 (p : Pattern) (guard : d129654 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 120 with
  | false =>
    have hg : d129653 p = 1 := by simpa only [d129654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10957 p hg
    simpa only [d129654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10959 (p : Pattern) (guard : d129655 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 118 with
  | false =>
    have hg : d129654 p = 1 := by simpa only [d129655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10958 p hg
    simpa only [d129655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10960 (p : Pattern) (guard : d129656 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 114 with
  | false =>
    have hg : d129655 p = 1 := by simpa only [d129656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10959 p hg
    simpa only [d129656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10961 (p : Pattern) (guard : d129657 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 111 with
  | false =>
    have hg : d129656 p = 1 := by simpa only [d129657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10960 p hg
    simpa only [d129657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10962 (p : Pattern) (guard : d129658 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 98 with
  | false =>
    have hg : d129657 p = 1 := by simpa only [d129658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10961 p hg
    simpa only [d129658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10963 (p : Pattern) (guard : d129659 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 97 with
  | false =>
    have hg : d129658 p = 1 := by simpa only [d129659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10962 p hg
    simpa only [d129659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10964 (p : Pattern) (guard : d129660 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 94 with
  | false =>
    have hg : d129659 p = 1 := by simpa only [d129660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10963 p hg
    simpa only [d129660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10965 (p : Pattern) (guard : d129661 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 76 with
  | false =>
    have hg : d129660 p = 1 := by simpa only [d129661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10964 p hg
    simpa only [d129661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10966 (p : Pattern) (guard : d129662 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 67 with
  | false =>
    have hg : d129661 p = 1 := by simpa only [d129662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10965 p hg
    simpa only [d129662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10967 (p : Pattern) (guard : d129663 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 52 with
  | false =>
    have hg : d129662 p = 1 := by simpa only [d129663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10966 p hg
    simpa only [d129663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10968 (p : Pattern) (guard : d129664 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 47 with
  | false =>
    have hg : d129663 p = 1 := by simpa only [d129664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10967 p hg
    simpa only [d129664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10969 (p : Pattern) (guard : d129665 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 46 with
  | false =>
    have hg : d129664 p = 1 := by simpa only [d129665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10968 p hg
    simpa only [d129665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10970 (p : Pattern) (guard : d129666 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 45 with
  | false =>
    have hg : d129665 p = 1 := by simpa only [d129666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10969 p hg
    simpa only [d129666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10971 (p : Pattern) (guard : d129667 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 30 with
  | false =>
    have hg : d129666 p = 1 := by simpa only [d129667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10970 p hg
    simpa only [d129667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10972 (p : Pattern) (guard : d129668 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 29 with
  | false =>
    have hg : d129667 p = 1 := by simpa only [d129668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10971 p hg
    simpa only [d129668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10973 (p : Pattern) (guard : d129669 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 28 with
  | false =>
    have hg : d129668 p = 1 := by simpa only [d129669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10972 p hg
    simpa only [d129669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10974 (p : Pattern) (guard : d129670 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 27 with
  | false =>
    have hg : d129669 p = 1 := by simpa only [d129670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10973 p hg
    simpa only [d129670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10975 (p : Pattern) (guard : d129671 p = 1) : d48308 p ≤ (0 : Int) + d47911 p := by
  cases selected : p 25 with
  | false =>
    have hg : d129670 p = 1 := by simpa only [d129671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10974 p hg
    simpa only [d129671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d129671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10632 p hg
    simpa only [d129671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10976 (p : Pattern) (guard : d0 p = 1) : d48308 p ≤ (-1 : Int) + d48997 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10977 (p : Pattern) (guard : d0 p = 1) : d48308 p ≤ (-2 : Int) + d48997 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10978 (p : Pattern) (guard : d0 p = 1) : d48308 p ≤ (3 : Int) + d130479 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10979 (p : Pattern) (guard : d0 p = 1) : d48308 p ≤ (2 : Int) + d130479 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10980 (p : Pattern) (guard : d0 p = 1) : d48308 p ≤ (-1 : Int) + d49102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10981 (p : Pattern) (guard : d0 p = 1) : d48308 p ≤ (-2 : Int) + d49102 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10982 (p : Pattern) (guard : d0 p = 1) : d48308 p ≤ (-1 : Int) + d48749 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10983 (p : Pattern) (guard : d0 p = 1) : d48308 p ≤ (-2 : Int) + d48749 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10984 (p : Pattern) (guard : d141012 p = 1) : d47866 p ≤ (1 : Int) + d47866 p := by
  omega
theorem compare10985 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (2 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10986 (p : Pattern) (guard : d151154 p = 1) : d47866 p ≤ (1 : Int) + d47866 p := by
  omega
theorem compare10987 (p : Pattern) (guard : d151284 p = 1) : d47866 p ≤ (0 : Int) + d47866 p := by
  omega
theorem compare10988 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d159795 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10989 (p : Pattern) (guard : d0 p = 1) : d47700 p ≤ (-1 : Int) + d159770 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10990 (p : Pattern) (guard : d0 p = 1) : d47697 p ≤ (-1 : Int) + d159767 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10991 (p : Pattern) (guard : d0 p = 1) : d47676 p ≤ (-1 : Int) + d100908 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10992 (p : Pattern) (guard : d0 p = 1) : d47681 p ≤ (-1 : Int) + d47680 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10993 (p : Pattern) (guard : d0 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10994 (p : Pattern) (guard : d0 p = 1) : d47655 p ≤ (-1 : Int) + d47683 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10995 (p : Pattern) (guard : d27 p = 1) : d47664 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d27, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10994 p hg
    simpa only [d27, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d26 p = 1 := by simpa only [d27, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4422 p hg
    simpa only [d27, d47664, d47684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10996 (p : Pattern) (guard : d0 p = 1) : d47684 p ≤ (-1 : Int) + d47684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare10997 (p : Pattern) (guard : d28 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 160 with
  | false =>
    have hg : d27 p = 1 := by simpa only [d28, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10995 p hg
    simpa only [d28, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d28, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10996 p hg
    simpa only [d28, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10998 (p : Pattern) (guard : d159796 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d159796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d159796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d28 p = 1 := by simpa only [d159796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10997 p hg
    simpa only [d159796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare10999 (p : Pattern) (guard : d159797 p = 1) : d47685 p ≤ (-1 : Int) + d47684 p := by
  cases selected : p 158 with
  | false =>
    have hg : d159796 p = 1 := by simpa only [d159797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10998 p hg
    simpa only [d159797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d159797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare10993 p hg
    simpa only [d159797, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
