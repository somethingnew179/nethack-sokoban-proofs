import NetHack.Soko22Hazard87.Compare033
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8500 (p : Pattern) (guard : d762 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8495 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7961 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8501 (p : Pattern) (guard : d763 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8496 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8500 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8502 (p : Pattern) (guard : d764 p = 1) : d47686 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d764, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7937 p hg
    simpa only [d764, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d763 p = 1 := by simpa only [d764, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8501 p hg
    simpa only [d764, d47686, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8503 (p : Pattern) (guard : d765 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7936 p hg
    simpa only [d765, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8502 p hg
    simpa only [d765, d47687, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8504 (p : Pattern) (guard : d766 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d761 p = 1 := by simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8499 p hg
    simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8503 p hg
    simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8505 (p : Pattern) (guard : d767 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8503 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8506 (p : Pattern) (guard : d768 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d766 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8504 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8505 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8507 (p : Pattern) (guard : d769 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8506 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8508 (p : Pattern) (guard : d770 p = 1) : d47699 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d770, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8507 p hg
    simpa only [d770, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7971 p hg
    simpa only [d770, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8509 (p : Pattern) (guard : d771 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d771, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d771, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d771, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8508 p hg
    simpa only [d771, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8510 (p : Pattern) (guard : d772 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8505 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8511 (p : Pattern) (guard : d773 p = 1) : d47687 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8510 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7967 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8512 (p : Pattern) (guard : d774 p = 1) : d47699 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8511 p hg
    simpa only [d774, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d47699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7971 p hg
    simpa only [d774, d47699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8513 (p : Pattern) (guard : d775 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d775, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d47700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8512 p hg
    simpa only [d775, d47700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8514 (p : Pattern) (guard : d776 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d771 p = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8509 p hg
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8513 p hg
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8515 (p : Pattern) (guard : d777 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d776 p = 1 := by simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8514 p hg
    simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8516 (p : Pattern) (guard : d778 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d777 p = 1 := by simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8515 p hg
    simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8517 (p : Pattern) (guard : d779 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d778 p = 1 := by simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8516 p hg
    simpa only [d779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8518 (p : Pattern) (guard : d780 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8513 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8519 (p : Pattern) (guard : d781 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8518 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8520 (p : Pattern) (guard : d782 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8519 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8521 (p : Pattern) (guard : d783 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d782 p = 1 := by simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8520 p hg
    simpa only [d783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8522 (p : Pattern) (guard : d784 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d779 p = 1 := by simpa only [d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8517 p hg
    simpa only [d784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d783 p = 1 := by simpa only [d784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8521 p hg
    simpa only [d784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8523 (p : Pattern) (guard : d785 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d784 p = 1 := by simpa only [d785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8522 p hg
    simpa only [d785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8524 (p : Pattern) (guard : d786 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d785 p = 1 := by simpa only [d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8523 p hg
    simpa only [d786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8525 (p : Pattern) (guard : d787 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d786 p = 1 := by simpa only [d787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8524 p hg
    simpa only [d787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8526 (p : Pattern) (guard : d788 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d787 p = 1 := by simpa only [d788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8525 p hg
    simpa only [d788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8527 (p : Pattern) (guard : d789 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d788 p = 1 := by simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8526 p hg
    simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8528 (p : Pattern) (guard : d792 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d778 p = 1 := by simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8516 p hg
    simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8529 (p : Pattern) (guard : d793 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d782 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8520 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8530 (p : Pattern) (guard : d794 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d792 p = 1 := by simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8528 p hg
    simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8529 p hg
    simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8531 (p : Pattern) (guard : d795 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8530 p hg
    simpa only [d795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8532 (p : Pattern) (guard : d796 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d795 p = 1 := by simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8531 p hg
    simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8533 (p : Pattern) (guard : d797 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d796 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8532 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8534 (p : Pattern) (guard : d798 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d797 p = 1 := by simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8533 p hg
    simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8535 (p : Pattern) (guard : d799 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d788 p = 1 := by simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8526 p hg
    simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8534 p hg
    simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8536 (p : Pattern) (guard : d800 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d789 p = 1 := by simpa only [d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8527 p hg
    simpa only [d800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d799 p = 1 := by simpa only [d800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8535 p hg
    simpa only [d800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8537 (p : Pattern) (guard : d801 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d800 p = 1 := by simpa only [d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8536 p hg
    simpa only [d801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8538 (p : Pattern) (guard : d53705 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d801 p = 1 := by simpa only [d53705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8537 p hg
    simpa only [d53705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8539 (p : Pattern) (guard : d53706 p = 1) : d47700 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53705 p = 1 := by simpa only [d53706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8538 p hg
    simpa only [d53706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8540 (p : Pattern) (guard : d528 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d309 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8345 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8541 (p : Pattern) (guard : d529 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8540 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d310 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8346 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8542 (p : Pattern) (guard : d530 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d529 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8541 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8347 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8543 (p : Pattern) (guard : d531 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8542 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8544 (p : Pattern) (guard : d532 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d531 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8543 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8545 (p : Pattern) (guard : d533 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8544 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d314 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8350 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8546 (p : Pattern) (guard : d534 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8180 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8547 (p : Pattern) (guard : d535 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8346 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d534 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8546 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8548 (p : Pattern) (guard : d536 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d535 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8547 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8182 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8549 (p : Pattern) (guard : d537 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d536 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8548 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8550 (p : Pattern) (guard : d538 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d537 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8549 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8004 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8551 (p : Pattern) (guard : d539 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d538 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8550 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8185 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8552 (p : Pattern) (guard : d540 p = 1) : d47706 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d533 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8545 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8551 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8553 (p : Pattern) (guard : d541 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d540 p = 1 := by simpa only [d541, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8552 p hg
    simpa only [d541, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d541, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8012 p hg
    simpa only [d541, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8554 (p : Pattern) (guard : d542 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8553 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8353 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8555 (p : Pattern) (guard : d543 p = 1) : d47735 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8554 p hg
    simpa only [d543, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d543, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8556 (p : Pattern) (guard : d544 p = 1) : d47736 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d543 p = 1 := by simpa only [d544, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8555 p hg
    simpa only [d544, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d544, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d544, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8557 (p : Pattern) (guard : d545 p = 1) : d47737 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d545, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8000 p hg
    simpa only [d545, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d545, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8556 p hg
    simpa only [d545, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8558 (p : Pattern) (guard : d546 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d545 p = 1 := by simpa only [d546, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8557 p hg
    simpa only [d546, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d546, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8021 p hg
    simpa only [d546, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8559 (p : Pattern) (guard : d547 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d546 p = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8558 p hg
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d322 p = 1 := by simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8358 p hg
    simpa only [d547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8560 (p : Pattern) (guard : d750 p = 1) : d47708 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8188 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8014 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8561 (p : Pattern) (guard : d751 p = 1) : d47735 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8560 p hg
    simpa only [d751, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d751, d47735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8562 (p : Pattern) (guard : d752 p = 1) : d47736 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d751 p = 1 := by simpa only [d752, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8561 p hg
    simpa only [d752, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d752, d47736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d752, d47736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8563 (p : Pattern) (guard : d753 p = 1) : d47737 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d753, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8000 p hg
    simpa only [d753, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d753, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8562 p hg
    simpa only [d753, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8564 (p : Pattern) (guard : d754 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d753 p = 1 := by simpa only [d754, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8563 p hg
    simpa only [d754, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d754, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8021 p hg
    simpa only [d754, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8565 (p : Pattern) (guard : d755 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d322 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8358 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d754 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8564 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8566 (p : Pattern) (guard : d756 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d547 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8559 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d755 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8565 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8567 (p : Pattern) (guard : d757 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d754 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8564 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8023 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8568 (p : Pattern) (guard : d758 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d755 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8565 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d757 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8567 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8569 (p : Pattern) (guard : d759 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d756 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8566 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d758 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8568 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8570 (p : Pattern) (guard : d760 p = 1) : d47756 p ≤ (-2 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d760, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7999 p hg
    simpa only [d760, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d759 p = 1 := by simpa only [d760, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8569 p hg
    simpa only [d760, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8571 (p : Pattern) (guard : d761 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d761, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7998 p hg
    simpa only [d761, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d760 p = 1 := by simpa only [d761, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8570 p hg
    simpa only [d761, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8572 (p : Pattern) (guard : d762 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 158 with
  | false =>
    have hg : d757 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8567 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8023 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8573 (p : Pattern) (guard : d763 p = 1) : d47755 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 157 with
  | false =>
    have hg : d758 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8568 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d762 p = 1 := by simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8572 p hg
    simpa only [d763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8574 (p : Pattern) (guard : d764 p = 1) : d47756 p ≤ (-2 : Int) + d47761 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d764, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7999 p hg
    simpa only [d764, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d763 p = 1 := by simpa only [d764, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8573 p hg
    simpa only [d764, d47756, d47761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8575 (p : Pattern) (guard : d765 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d765, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7998 p hg
    simpa only [d765, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d764 p = 1 := by simpa only [d765, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8574 p hg
    simpa only [d765, d47757, d47762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8576 (p : Pattern) (guard : d766 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d761 p = 1 := by simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8571 p hg
    simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d765 p = 1 := by simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8575 p hg
    simpa only [d766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8577 (p : Pattern) (guard : d767 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 136 with
  | false =>
    have hg : d765 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8575 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8578 (p : Pattern) (guard : d768 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d766 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8576 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d767 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8577 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8579 (p : Pattern) (guard : d769 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d768 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8578 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8580 (p : Pattern) (guard : d770 p = 1) : d47765 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d769 p = 1 := by simpa only [d770, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8579 p hg
    simpa only [d770, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d770, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8033 p hg
    simpa only [d770, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8581 (p : Pattern) (guard : d771 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d771, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7997 p hg
    simpa only [d771, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d770 p = 1 := by simpa only [d771, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8580 p hg
    simpa only [d771, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8582 (p : Pattern) (guard : d772 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 135 with
  | false =>
    have hg : d767 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8577 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8583 (p : Pattern) (guard : d773 p = 1) : d47757 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 119 with
  | false =>
    have hg : d772 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8582 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8029 p hg
    simpa only [d773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8584 (p : Pattern) (guard : d774 p = 1) : d47765 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 116 with
  | false =>
    have hg : d773 p = 1 := by simpa only [d774, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8583 p hg
    simpa only [d774, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d774, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8033 p hg
    simpa only [d774, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8585 (p : Pattern) (guard : d775 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d775, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7997 p hg
    simpa only [d775, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d774 p = 1 := by simpa only [d775, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8584 p hg
    simpa only [d775, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8586 (p : Pattern) (guard : d776 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d771 p = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8581 p hg
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d775 p = 1 := by simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8585 p hg
    simpa only [d776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8587 (p : Pattern) (guard : d777 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d776 p = 1 := by simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8586 p hg
    simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8588 (p : Pattern) (guard : d778 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d777 p = 1 := by simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8587 p hg
    simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8589 (p : Pattern) (guard : d792 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d778 p = 1 := by simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8588 p hg
    simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8590 (p : Pattern) (guard : d780 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 113 with
  | false =>
    have hg : d775 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8585 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8591 (p : Pattern) (guard : d781 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 96 with
  | false =>
    have hg : d780 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8590 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8592 (p : Pattern) (guard : d782 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 95 with
  | false =>
    have hg : d781 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8591 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8593 (p : Pattern) (guard : d793 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 93 with
  | false =>
    have hg : d782 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8592 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8594 (p : Pattern) (guard : d794 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 91 with
  | false =>
    have hg : d792 p = 1 := by simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8589 p hg
    simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d793 p = 1 := by simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8593 p hg
    simpa only [d794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8595 (p : Pattern) (guard : d795 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d794 p = 1 := by simpa only [d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8594 p hg
    simpa only [d795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8596 (p : Pattern) (guard : d796 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 89 with
  | false =>
    have hg : d795 p = 1 := by simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8595 p hg
    simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8597 (p : Pattern) (guard : d797 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d796 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8596 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8598 (p : Pattern) (guard : d798 p = 1) : d47766 p ≤ (-2 : Int) + d47762 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7996 p hg
    simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d797 p = 1 := by simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8597 p hg
    simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8599 (p : Pattern) (guard : d53707 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53707, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53707, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d798 p = 1 := by simpa only [d53707, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8598 p hg
    simpa only [d53707, d47767, d98792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8600 (p : Pattern) (guard : d53708 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53707 p = 1 := by simpa only [d53708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8599 p hg
    simpa only [d53708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8601 (p : Pattern) (guard : d53709 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 69 with
  | false =>
    have hg : d53708 p = 1 := by simpa only [d53709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8600 p hg
    simpa only [d53709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8602 (p : Pattern) (guard : d53710 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 51 with
  | false =>
    have hg : d53709 p = 1 := by simpa only [d53710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8601 p hg
    simpa only [d53710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8603 (p : Pattern) (guard : d53711 p = 1) : d47767 p ≤ (-2 : Int) + d98792 p := by
  cases selected : p 50 with
  | false =>
    have hg : d53710 p = 1 := by simpa only [d53711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8602 p hg
    simpa only [d53711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7995 p hg
    simpa only [d53711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8604 (p : Pattern) (guard : d53712 p = 1) : d47768 p ≤ (-2 : Int) + d98793 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53706 p = 1 := by simpa only [d53712, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8539 p hg
    simpa only [d53712, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53711 p = 1 := by simpa only [d53712, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8603 p hg
    simpa only [d53712, d47768, d98793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8605 (p : Pattern) (guard : d528 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d309 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8396 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8606 (p : Pattern) (guard : d529 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8605 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d310 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8397 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8607 (p : Pattern) (guard : d530 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d529 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8606 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8398 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8608 (p : Pattern) (guard : d531 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8607 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8609 (p : Pattern) (guard : d532 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d531 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8608 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8610 (p : Pattern) (guard : d533 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8609 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d314 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8401 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8611 (p : Pattern) (guard : d534 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8222 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8612 (p : Pattern) (guard : d535 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8397 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d534 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8611 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8613 (p : Pattern) (guard : d536 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d535 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8612 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8224 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8614 (p : Pattern) (guard : d537 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d536 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8613 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8615 (p : Pattern) (guard : d538 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d537 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8614 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8059 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8616 (p : Pattern) (guard : d539 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d538 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8615 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8227 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8617 (p : Pattern) (guard : d540 p = 1) : d47630 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d533 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8610 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8616 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8618 (p : Pattern) (guard : d541 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d540 p = 1 := by simpa only [d541, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8617 p hg
    simpa only [d541, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d541, d47652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8067 p hg
    simpa only [d541, d47652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8619 (p : Pattern) (guard : d542 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8618 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8404 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8620 (p : Pattern) (guard : d659 p = 1) : d47652 p ≤ (-2 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d659, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d659, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d542 p = 1 := by simpa only [d659, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8619 p hg
    simpa only [d659, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8621 (p : Pattern) (guard : d543 p = 1) : d47797 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8482 p hg
    simpa only [d543, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d543, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8622 (p : Pattern) (guard : d660 p = 1) : d47798 p ≤ (-2 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d659 p = 1 := by simpa only [d660, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8620 p hg
    simpa only [d660, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d543 p = 1 := by simpa only [d660, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8621 p hg
    simpa only [d660, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8623 (p : Pattern) (guard : d528 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d309 p = 1 := by simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8412 p hg
    simpa only [d528, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8624 (p : Pattern) (guard : d529 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8623 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d310 p = 1 := by simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8413 p hg
    simpa only [d529, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8625 (p : Pattern) (guard : d530 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d529 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8624 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d311 p = 1 := by simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8414 p hg
    simpa only [d530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8626 (p : Pattern) (guard : d531 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8625 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8627 (p : Pattern) (guard : d532 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d531 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8626 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d532, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8628 (p : Pattern) (guard : d533 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d532 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8627 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d314 p = 1 := by simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8417 p hg
    simpa only [d533, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8629 (p : Pattern) (guard : d534 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d129 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8238 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8630 (p : Pattern) (guard : d535 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d310 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8413 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d534 p = 1 := by simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8629 p hg
    simpa only [d535, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8631 (p : Pattern) (guard : d536 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d535 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8630 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d131 p = 1 := by simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8240 p hg
    simpa only [d536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8632 (p : Pattern) (guard : d537 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d536 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8631 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d537, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8633 (p : Pattern) (guard : d538 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d537 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8632 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8077 p hg
    simpa only [d538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8634 (p : Pattern) (guard : d539 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d538 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8633 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d134 p = 1 := by simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8243 p hg
    simpa only [d539, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8635 (p : Pattern) (guard : d540 p = 1) : d47634 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d533 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8628 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8634 p hg
    simpa only [d540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8636 (p : Pattern) (guard : d541 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d540 p = 1 := by simpa only [d541, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8635 p hg
    simpa only [d541, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d541, d47677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8085 p hg
    simpa only [d541, d47677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8637 (p : Pattern) (guard : d542 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d541 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8636 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d317 p = 1 := by simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8420 p hg
    simpa only [d542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8638 (p : Pattern) (guard : d543 p = 1) : d47682 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d542 p = 1 := by simpa only [d543, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8637 p hg
    simpa only [d543, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d543, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d543, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8639 (p : Pattern) (guard : d544 p = 1) : d47683 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d543 p = 1 := by simpa only [d544, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8638 p hg
    simpa only [d544, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d544, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d544, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8640 (p : Pattern) (guard : d661 p = 1) : d47799 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d660 p = 1 := by simpa only [d661, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8622 p hg
    simpa only [d661, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d544 p = 1 := by simpa only [d661, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8639 p hg
    simpa only [d661, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8641 (p : Pattern) (guard : d662 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d661 p = 1 := by simpa only [d662, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8640 p hg
    simpa only [d662, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d662, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d662, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8642 (p : Pattern) (guard : d663 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d662 p = 1 := by simpa only [d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8641 p hg
    simpa only [d663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d415 p = 1 := by simpa only [d663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8425 p hg
    simpa only [d663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8643 (p : Pattern) (guard : d750 p = 1) : d47652 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8230 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8069 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8644 (p : Pattern) (guard : d971 p = 1) : d47652 p ≤ (-2 : Int) + d47662 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d971, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8055 p hg
    simpa only [d971, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d750 p = 1 := by simpa only [d971, d47662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8643 p hg
    simpa only [d971, d47662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8645 (p : Pattern) (guard : d751 p = 1) : d47797 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8488 p hg
    simpa only [d751, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8016 p hg
    simpa only [d751, d47797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8646 (p : Pattern) (guard : d972 p = 1) : d47798 p ≤ (-2 : Int) + d47690 p := by
  cases selected : p 162 with
  | false =>
    have hg : d971 p = 1 := by simpa only [d972, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8644 p hg
    simpa only [d972, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d751 p = 1 := by simpa only [d972, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8645 p hg
    simpa only [d972, d47798, d47690, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8647 (p : Pattern) (guard : d750 p = 1) : d47677 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d137 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8246 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8087 p hg
    simpa only [d750, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8648 (p : Pattern) (guard : d751 p = 1) : d47682 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d750 p = 1 := by simpa only [d751, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8647 p hg
    simpa only [d751, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d751, d47682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d751, d47682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8649 (p : Pattern) (guard : d752 p = 1) : d47683 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d751 p = 1 := by simpa only [d752, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8648 p hg
    simpa only [d752, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d752, d47683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d752, d47683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8650 (p : Pattern) (guard : d973 p = 1) : d47799 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d972 p = 1 := by simpa only [d973, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8646 p hg
    simpa only [d973, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d752 p = 1 := by simpa only [d973, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8649 p hg
    simpa only [d973, d47799, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8651 (p : Pattern) (guard : d974 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d973 p = 1 := by simpa only [d974, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8650 p hg
    simpa only [d974, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d974, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8092 p hg
    simpa only [d974, d47803, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8652 (p : Pattern) (guard : d975 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d415 p = 1 := by simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8425 p hg
    simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d974 p = 1 := by simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8651 p hg
    simpa only [d975, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8653 (p : Pattern) (guard : d976 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d663 p = 1 := by simpa only [d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8642 p hg
    simpa only [d976, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d975 p = 1 := by simpa only [d976, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8652 p hg
    simpa only [d976, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8654 (p : Pattern) (guard : d980 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d974 p = 1 := by simpa only [d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8651 p hg
    simpa only [d980, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d980, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8094 p hg
    simpa only [d980, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8655 (p : Pattern) (guard : d981 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d975 p = 1 := by simpa only [d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8652 p hg
    simpa only [d981, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d980 p = 1 := by simpa only [d981, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8654 p hg
    simpa only [d981, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8656 (p : Pattern) (guard : d982 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d976 p = 1 := by simpa only [d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8653 p hg
    simpa only [d982, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d981 p = 1 := by simpa only [d982, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8655 p hg
    simpa only [d982, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8657 (p : Pattern) (guard : d983 p = 1) : d47804 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d983, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8054 p hg
    simpa only [d983, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d982 p = 1 := by simpa only [d983, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8656 p hg
    simpa only [d983, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8658 (p : Pattern) (guard : d984 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d984, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8053 p hg
    simpa only [d984, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d983 p = 1 := by simpa only [d984, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8657 p hg
    simpa only [d984, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8659 (p : Pattern) (guard : d986 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 158 with
  | false =>
    have hg : d980 p = 1 := by simpa only [d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8654 p hg
    simpa only [d986, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d986, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8094 p hg
    simpa only [d986, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8660 (p : Pattern) (guard : d987 p = 1) : d47803 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 157 with
  | false =>
    have hg : d981 p = 1 := by simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8655 p hg
    simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d986 p = 1 := by simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8659 p hg
    simpa only [d987, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8661 (p : Pattern) (guard : d988 p = 1) : d47804 p ≤ (-2 : Int) + d47695 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d988, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8054 p hg
    simpa only [d988, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d987 p = 1 := by simpa only [d988, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8660 p hg
    simpa only [d988, d47804, d47695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8662 (p : Pattern) (guard : d989 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d989, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8053 p hg
    simpa only [d989, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d988 p = 1 := by simpa only [d989, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8661 p hg
    simpa only [d989, d47805, d47696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8663 (p : Pattern) (guard : d990 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d984 p = 1 := by simpa only [d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8658 p hg
    simpa only [d990, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d989 p = 1 := by simpa only [d990, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8662 p hg
    simpa only [d990, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8664 (p : Pattern) (guard : d995 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 136 with
  | false =>
    have hg : d989 p = 1 := by simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8662 p hg
    simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d995, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8665 (p : Pattern) (guard : d996 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d990 p = 1 := by simpa only [d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8663 p hg
    simpa only [d996, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d995 p = 1 := by simpa only [d996, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8664 p hg
    simpa only [d996, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8666 (p : Pattern) (guard : d997 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d996 p = 1 := by simpa only [d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8665 p hg
    simpa only [d997, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d997, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d997, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8667 (p : Pattern) (guard : d998 p = 1) : d47807 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d997 p = 1 := by simpa only [d998, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8666 p hg
    simpa only [d998, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d998, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8104 p hg
    simpa only [d998, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8668 (p : Pattern) (guard : d999 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d999, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d999, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d998 p = 1 := by simpa only [d999, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8667 p hg
    simpa only [d999, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8669 (p : Pattern) (guard : d1004 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 135 with
  | false =>
    have hg : d995 p = 1 := by simpa only [d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8664 p hg
    simpa only [d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d1004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8670 (p : Pattern) (guard : d1005 p = 1) : d47805 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 119 with
  | false =>
    have hg : d1004 p = 1 := by simpa only [d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8669 p hg
    simpa only [d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8100 p hg
    simpa only [d1005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8671 (p : Pattern) (guard : d1006 p = 1) : d47807 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 116 with
  | false =>
    have hg : d1005 p = 1 := by simpa only [d1006, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8670 p hg
    simpa only [d1006, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1006, d47807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8104 p hg
    simpa only [d1006, d47807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8672 (p : Pattern) (guard : d1007 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1007, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7935 p hg
    simpa only [d1007, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1006 p = 1 := by simpa only [d1007, d47808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8671 p hg
    simpa only [d1007, d47808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8673 (p : Pattern) (guard : d1008 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d999 p = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8668 p hg
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1007 p = 1 := by simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8672 p hg
    simpa only [d1008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8674 (p : Pattern) (guard : d1009 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1008 p = 1 := by simpa only [d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8673 p hg
    simpa only [d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d1009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8675 (p : Pattern) (guard : d1010 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1009 p = 1 := by simpa only [d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8674 p hg
    simpa only [d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d1010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8676 (p : Pattern) (guard : d1011 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1010 p = 1 := by simpa only [d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8675 p hg
    simpa only [d1011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d1011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8677 (p : Pattern) (guard : d1060 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1007 p = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8672 p hg
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d1060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8678 (p : Pattern) (guard : d1061 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 96 with
  | false =>
    have hg : d1060 p = 1 := by simpa only [d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8677 p hg
    simpa only [d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8679 (p : Pattern) (guard : d1062 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 95 with
  | false =>
    have hg : d1061 p = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8678 p hg
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8680 (p : Pattern) (guard : d1063 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 93 with
  | false =>
    have hg : d1062 p = 1 := by simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8679 p hg
    simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d1063, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8681 (p : Pattern) (guard : d53713 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 91 with
  | false =>
    have hg : d1011 p = 1 := by simpa only [d53713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8676 p hg
    simpa only [d53713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1063 p = 1 := by simpa only [d53713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8680 p hg
    simpa only [d53713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8682 (p : Pattern) (guard : d53714 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53713 p = 1 := by simpa only [d53714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8681 p hg
    simpa only [d53714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8683 (p : Pattern) (guard : d53715 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 89 with
  | false =>
    have hg : d53714 p = 1 := by simpa only [d53715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8682 p hg
    simpa only [d53715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8684 (p : Pattern) (guard : d53716 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53715 p = 1 := by simpa only [d53716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8683 p hg
    simpa only [d53716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8685 (p : Pattern) (guard : d53717 p = 1) : d47808 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8052 p hg
    simpa only [d53717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53716 p = 1 := by simpa only [d53717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8684 p hg
    simpa only [d53717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8686 (p : Pattern) (guard : d53718 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53718, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7934 p hg
    simpa only [d53718, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53717 p = 1 := by simpa only [d53718, d47809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8685 p hg
    simpa only [d53718, d47809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8687 (p : Pattern) (guard : d53719 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53718 p = 1 := by simpa only [d53719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8686 p hg
    simpa only [d53719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8688 (p : Pattern) (guard : d53720 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 69 with
  | false =>
    have hg : d53719 p = 1 := by simpa only [d53720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8687 p hg
    simpa only [d53720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8689 (p : Pattern) (guard : d53721 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 51 with
  | false =>
    have hg : d53720 p = 1 := by simpa only [d53721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8688 p hg
    simpa only [d53721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8690 (p : Pattern) (guard : d53722 p = 1) : d47809 p ≤ (-2 : Int) + d47696 p := by
  cases selected : p 50 with
  | false =>
    have hg : d53721 p = 1 := by simpa only [d53722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8689 p hg
    simpa only [d53722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8051 p hg
    simpa only [d53722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8691 (p : Pattern) (guard : d53723 p = 1) : d47865 p ≤ (-2 : Int) + d98795 p := by
  cases selected : p 49 with
  | false =>
    have hg : d53722 p = 1 := by simpa only [d53723, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8690 p hg
    simpa only [d53723, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d53723, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8121 p hg
    simpa only [d53723, d47865, d98795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8692 (p : Pattern) (guard : d53724 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 48 with
  | false =>
    have hg : d53712 p = 1 := by simpa only [d53724, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8604 p hg
    simpa only [d53724, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53723 p = 1 := by simpa only [d53724, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8691 p hg
    simpa only [d53724, d47866, d98796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8693 (p : Pattern) (guard : d53725 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53724 p = 1 := by simpa only [d53725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8692 p hg
    simpa only [d53725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8694 (p : Pattern) (guard : d53726 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53725 p = 1 := by simpa only [d53726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8693 p hg
    simpa only [d53726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8695 (p : Pattern) (guard : d53727 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53726 p = 1 := by simpa only [d53727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8694 p hg
    simpa only [d53727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8696 (p : Pattern) (guard : d53728 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53727 p = 1 := by simpa only [d53728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8695 p hg
    simpa only [d53728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8697 (p : Pattern) (guard : d53729 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53728 p = 1 := by simpa only [d53729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8696 p hg
    simpa only [d53729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8698 (p : Pattern) (guard : d53730 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53729 p = 1 := by simpa only [d53730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8697 p hg
    simpa only [d53730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8699 (p : Pattern) (guard : d53731 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d53731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7933 p hg
    simpa only [d53731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53730 p = 1 := by simpa only [d53731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8698 p hg
    simpa only [d53731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8700 (p : Pattern) (guard : d53732 p = 1) : d47866 p ≤ (-2 : Int) + d98796 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d53704 p = 1 := by simpa only [d53732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8467 p hg
    simpa only [d53732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d53731 p = 1 := by simpa only [d53732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8699 p hg
    simpa only [d53732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8701 (p : Pattern) (guard : d820 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d528 p = 1 := by simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8468 p hg
    simpa only [d820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8702 (p : Pattern) (guard : d821 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d820 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8701 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d529 p = 1 := by simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8469 p hg
    simpa only [d821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8703 (p : Pattern) (guard : d822 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d821 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8702 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8704 (p : Pattern) (guard : d823 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d822 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8703 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8705 (p : Pattern) (guard : d0 p = 1) : d4 p ≤ (-2 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8706 (p : Pattern) (guard : d1084 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1084, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8705 p hg
    simpa only [d1084, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d14 p = 1 := by simpa only [d1084, d47617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8131 p hg
    simpa only [d1084, d47617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8707 (p : Pattern) (guard : d1085 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1084 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8706 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1085, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8708 (p : Pattern) (guard : d1086 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1085 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8707 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1086, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8709 (p : Pattern) (guard : d1087 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1086 p = 1 := by simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8708 p hg
    simpa only [d1087, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8710 (p : Pattern) (guard : d1088 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d530 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8470 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1087 p = 1 := by simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8709 p hg
    simpa only [d1088, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8711 (p : Pattern) (guard : d1089 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1088 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8710 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8712 (p : Pattern) (guard : d1090 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d823 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8704 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1089 p = 1 := by simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8711 p hg
    simpa only [d1090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8713 (p : Pattern) (guard : d825 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 226 with
  | false =>
    have hg : d309 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8287 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8714 (p : Pattern) (guard : d826 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d528 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8468 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d825 p = 1 := by simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8713 p hg
    simpa only [d826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8715 (p : Pattern) (guard : d827 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d826 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8714 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d535 p = 1 := by simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8475 p hg
    simpa only [d827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8716 (p : Pattern) (guard : d828 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d827 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8715 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8717 (p : Pattern) (guard : d829 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d828 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8716 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8718 (p : Pattern) (guard : d830 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d829 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8717 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d538 p = 1 := by simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8478 p hg
    simpa only [d830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8719 (p : Pattern) (guard : d1091 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1090 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8712 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d830 p = 1 := by simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8718 p hg
    simpa only [d1091, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8720 (p : Pattern) (guard : d1092 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1091 p = 1 := by simpa only [d1092, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8719 p hg
    simpa only [d1092, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1092, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7950 p hg
    simpa only [d1092, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8721 (p : Pattern) (guard : d1093 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1086 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8708 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d17 p = 1 := by simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7944 p hg
    simpa only [d1093, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8722 (p : Pattern) (guard : d1094 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d312 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8290 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1093 p = 1 := by simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8721 p hg
    simpa only [d1094, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8723 (p : Pattern) (guard : d1095 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1094 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8722 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1095, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8724 (p : Pattern) (guard : d1096 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1089 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8711 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1095 p = 1 := by simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8723 p hg
    simpa only [d1096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8725 (p : Pattern) (guard : d1097 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1096 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8724 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d539 p = 1 := by simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8479 p hg
    simpa only [d1097, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8726 (p : Pattern) (guard : d1098 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1097 p = 1 := by simpa only [d1098, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8725 p hg
    simpa only [d1098, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1098, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7950 p hg
    simpa only [d1098, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8727 (p : Pattern) (guard : d1099 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1092 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8720 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1098 p = 1 := by simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8726 p hg
    simpa only [d1099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8728 (p : Pattern) (guard : d1100 p = 1) : d47660 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1099 p = 1 := by simpa only [d1100, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8727 p hg
    simpa only [d1100, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1100, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7954 p hg
    simpa only [d1100, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8729 (p : Pattern) (guard : d1101 p = 1) : d47663 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1100 p = 1 := by simpa only [d1101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8728 p hg
    simpa only [d1101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7956 p hg
    simpa only [d1101, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8730 (p : Pattern) (guard : d1102 p = 1) : d47664 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1102, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d1102, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1101 p = 1 := by simpa only [d1102, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8729 p hg
    simpa only [d1102, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8731 (p : Pattern) (guard : d1103 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1102 p = 1 := by simpa only [d1103, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8730 p hg
    simpa only [d1103, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1103, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7959 p hg
    simpa only [d1103, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8732 (p : Pattern) (guard : d1104 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d132 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8135 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7945 p hg
    simpa only [d1104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8733 (p : Pattern) (guard : d1105 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1104 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8732 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8734 (p : Pattern) (guard : d1106 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1095 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8723 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1105 p = 1 := by simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8733 p hg
    simpa only [d1106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8735 (p : Pattern) (guard : d1107 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1106 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8734 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d135 p = 1 := by simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8138 p hg
    simpa only [d1107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8736 (p : Pattern) (guard : d1108 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1107 p = 1 := by simpa only [d1108, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8735 p hg
    simpa only [d1108, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1108, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7950 p hg
    simpa only [d1108, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8737 (p : Pattern) (guard : d1109 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1098 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8726 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1108 p = 1 := by simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8736 p hg
    simpa only [d1109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8738 (p : Pattern) (guard : d1110 p = 1) : d47660 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1109 p = 1 := by simpa only [d1110, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8737 p hg
    simpa only [d1110, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1110, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7954 p hg
    simpa only [d1110, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8739 (p : Pattern) (guard : d1111 p = 1) : d47663 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1110 p = 1 := by simpa only [d1111, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8738 p hg
    simpa only [d1111, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1111, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7956 p hg
    simpa only [d1111, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8740 (p : Pattern) (guard : d1112 p = 1) : d47664 p ≤ (-2 : Int) + d47692 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1112, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7938 p hg
    simpa only [d1112, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1111 p = 1 := by simpa only [d1112, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8739 p hg
    simpa only [d1112, d47664, d47692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8741 (p : Pattern) (guard : d1113 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 160 with
  | false =>
    have hg : d1112 p = 1 := by simpa only [d1113, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d1113, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1113, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7959 p hg
    simpa only [d1113, d47685, d47694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8742 (p : Pattern) (guard : d1114 p = 1) : d47685 p ≤ (-2 : Int) + d47694 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1103 p = 1 := by simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8731 p hg
    simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1113 p = 1 := by simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8741 p hg
    simpa only [d1114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8743 (p : Pattern) (guard : d1115 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18 p = 1 := by simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7945 p hg
    simpa only [d1115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8744 (p : Pattern) (guard : d1116 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1115 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8743 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7942 p hg
    simpa only [d1116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8745 (p : Pattern) (guard : d1117 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1116 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8744 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7947 p hg
    simpa only [d1117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8746 (p : Pattern) (guard : d1118 p = 1) : d47617 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1117 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8745 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d21 p = 1 := by simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7948 p hg
    simpa only [d1118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8747 (p : Pattern) (guard : d1119 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1118 p = 1 := by simpa only [d1119, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8746 p hg
    simpa only [d1119, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1119, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7950 p hg
    simpa only [d1119, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8748 (p : Pattern) (guard : d1120 p = 1) : d47619 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1108 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8736 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1119 p = 1 := by simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8747 p hg
    simpa only [d1120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8749 (p : Pattern) (guard : d1121 p = 1) : d47660 p ≤ (-2 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1120 p = 1 := by simpa only [d1121, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8748 p hg
    simpa only [d1121, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1121, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7954 p hg
    simpa only [d1121, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
