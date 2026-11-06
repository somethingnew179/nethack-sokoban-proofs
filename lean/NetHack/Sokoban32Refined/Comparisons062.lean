/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons061
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8680 (p : Pattern) (guard : d1293 p = 1) : d790 p ≤ (0 : Int) + d719 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8677 p hg
    simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8679 p hg
    simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8681 (p : Pattern) (guard : d1293 p = 1) : d791 p ≤ (0 : Int) + d719 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8679 p hg
    simpa only [d791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8678 p hg
    simpa only [d791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8682 (p : Pattern) (guard : d1293 p = 1) : d792 p ≤ (0 : Int) + d719 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8680 p hg
    simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8681 p hg
    simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8683 (p : Pattern) (guard : d1293 p = 1) : d793 p ≤ (0 : Int) + d720 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d793, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8648 p hg
    simpa only [d793, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d793, d720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8682 p hg
    simpa only [d793, d720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8684 (p : Pattern) (guard : d1293 p = 1) : d794 p ≤ (0 : Int) + d705 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d794, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8638 p hg
    simpa only [d794, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d794, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d794, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8685 (p : Pattern) (guard : d1293 p = 1) : d795 p ≤ (0 : Int) + d706 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d795, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8638 p hg
    simpa only [d795, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d795, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8684 p hg
    simpa only [d795, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8686 (p : Pattern) (guard : d1293 p = 1) : d796 p ≤ (0 : Int) + d706 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8685 p hg
    simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8664 p hg
    simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8687 (p : Pattern) (guard : d1293 p = 1) : d797 p ≤ (0 : Int) + d706 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8685 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8686 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8688 (p : Pattern) (guard : d1293 p = 1) : d798 p ≤ (0 : Int) + d706 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8686 p hg
    simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8664 p hg
    simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8689 (p : Pattern) (guard : d1293 p = 1) : d799 p ≤ (0 : Int) + d706 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8687 p hg
    simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8688 p hg
    simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8690 (p : Pattern) (guard : d1293 p = 1) : d800 p ≤ (0 : Int) + d721 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d800, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8683 p hg
    simpa only [d800, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d800, d721, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8689 p hg
    simpa only [d800, d721, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8691 (p : Pattern) (guard : d1293 p = 1) : d801 p ≤ (0 : Int) + d722 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d801, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8679 p hg
    simpa only [d801, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d801, d722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8663 p hg
    simpa only [d801, d722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8692 (p : Pattern) (guard : d1293 p = 1) : d802 p ≤ (0 : Int) + d723 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d802, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8680 p hg
    simpa only [d802, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d802, d723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8691 p hg
    simpa only [d802, d723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8693 (p : Pattern) (guard : d1293 p = 1) : d803 p ≤ (0 : Int) + d724 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d803, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8668 p hg
    simpa only [d803, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d803, d724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8692 p hg
    simpa only [d803, d724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8694 (p : Pattern) (guard : d1293 p = 1) : d804 p ≤ (0 : Int) + d725 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d804, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8686 p hg
    simpa only [d804, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d804, d725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d804, d725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8695 (p : Pattern) (guard : d1293 p = 1) : d805 p ≤ (0 : Int) + d726 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d805, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8687 p hg
    simpa only [d805, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d805, d726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8694 p hg
    simpa only [d805, d726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8696 (p : Pattern) (guard : d1293 p = 1) : d806 p ≤ (0 : Int) + d705 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8684 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8663 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8697 (p : Pattern) (guard : d1293 p = 1) : d807 p ≤ (0 : Int) + d705 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8684 p hg
    simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8696 p hg
    simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8698 (p : Pattern) (guard : d1293 p = 1) : d808 p ≤ (0 : Int) + d727 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d808, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8696 p hg
    simpa only [d808, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d808, d727, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d808, d727, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8699 (p : Pattern) (guard : d1293 p = 1) : d809 p ≤ (0 : Int) + d728 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d809, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8697 p hg
    simpa only [d809, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d809, d728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8698 p hg
    simpa only [d809, d728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8700 (p : Pattern) (guard : d1293 p = 1) : d810 p ≤ (0 : Int) + d729 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d810, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8695 p hg
    simpa only [d810, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d810, d729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8699 p hg
    simpa only [d810, d729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8701 (p : Pattern) (guard : d1293 p = 1) : d811 p ≤ (0 : Int) + d730 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d811, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8693 p hg
    simpa only [d811, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d811, d730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8700 p hg
    simpa only [d811, d730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8702 (p : Pattern) (guard : d1293 p = 1) : d812 p ≤ (0 : Int) + d731 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d812, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8690 p hg
    simpa only [d812, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d812, d731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8701 p hg
    simpa only [d812, d731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8703 (p : Pattern) (guard : d1293 p = 1) : d813 p ≤ (0 : Int) + d732 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d813, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8676 p hg
    simpa only [d813, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d813, d732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8702 p hg
    simpa only [d813, d732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8704 (p : Pattern) (guard : d1293 p = 1) : d814 p ≤ (0 : Int) + d733 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d814, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8668 p hg
    simpa only [d814, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d814, d733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8674 p hg
    simpa only [d814, d733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8705 (p : Pattern) (guard : d1293 p = 1) : d815 p ≤ (0 : Int) + d734 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d815, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8662 p hg
    simpa only [d815, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d815, d734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8704 p hg
    simpa only [d815, d734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8706 (p : Pattern) (guard : d1293 p = 1) : d816 p ≤ (0 : Int) + d705 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8696 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8663 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8707 (p : Pattern) (guard : d1293 p = 1) : d817 p ≤ (0 : Int) + d705 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8697 p hg
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8706 p hg
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8708 (p : Pattern) (guard : d1293 p = 1) : d818 p ≤ (0 : Int) + d735 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d818, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8689 p hg
    simpa only [d818, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d818, d735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8707 p hg
    simpa only [d818, d735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8709 (p : Pattern) (guard : d1293 p = 1) : d819 p ≤ (0 : Int) + d736 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d819, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8683 p hg
    simpa only [d819, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d819, d736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8708 p hg
    simpa only [d819, d736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8710 (p : Pattern) (guard : d1293 p = 1) : d820 p ≤ (0 : Int) + d737 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d820, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8668 p hg
    simpa only [d820, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d820, d737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8673 p hg
    simpa only [d820, d737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8711 (p : Pattern) (guard : d1293 p = 1) : d821 p ≤ (0 : Int) + d738 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d821, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8699 p hg
    simpa only [d821, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d821, d738, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d821, d738, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8712 (p : Pattern) (guard : d1293 p = 1) : d822 p ≤ (0 : Int) + d739 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d822, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8710 p hg
    simpa only [d822, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d822, d739, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8711 p hg
    simpa only [d822, d739, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8713 (p : Pattern) (guard : d1293 p = 1) : d823 p ≤ (0 : Int) + d740 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d823, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8709 p hg
    simpa only [d823, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d823, d740, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8712 p hg
    simpa only [d823, d740, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8714 (p : Pattern) (guard : d1293 p = 1) : d824 p ≤ (0 : Int) + d741 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d824, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8705 p hg
    simpa only [d824, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d824, d741, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8713 p hg
    simpa only [d824, d741, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8715 (p : Pattern) (guard : d1293 p = 1) : d825 p ≤ (0 : Int) + d742 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d825, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8703 p hg
    simpa only [d825, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d825, d742, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8714 p hg
    simpa only [d825, d742, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8716 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (2 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8717 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8718 (p : Pattern) (guard : d985 p = 1) : d3 p ≤ (2 : Int) + d0 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4307 p hg
    simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8717 p hg
    simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8719 (p : Pattern) (guard : d1552 p = 1) : d3 p ≤ (2 : Int) + d0 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8716 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8718 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8720 (p : Pattern) (guard : d0 p = 1) : d17 p ≤ (2 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8721 (p : Pattern) (guard : d1553 p = 1) : d743 p ≤ (2 : Int) + d0 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8719 p hg
    simpa only [d1553, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8720 p hg
    simpa only [d1553, d743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8722 (p : Pattern) (guard : d0 p = 1) : d3 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8723 (p : Pattern) (guard : d985 p = 1) : d3 p ≤ (2 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4372 p hg
    simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4429 p hg
    simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8724 (p : Pattern) (guard : d1552 p = 1) : d3 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8722 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8723 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8725 (p : Pattern) (guard : d1553 p = 1) : d744 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8724 p hg
    simpa only [d1553, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4429 p hg
    simpa only [d1553, d744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8726 (p : Pattern) (guard : d1553 p = 1) : d745 p ≤ (2 : Int) + d1816 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d745, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8721 p hg
    simpa only [d745, d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d745, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8725 p hg
    simpa only [d745, d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8727 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (2 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8728 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (2 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8729 (p : Pattern) (guard : d985 p = 1) : d9 p ≤ (2 : Int) + d1 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4316 p hg
    simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8728 p hg
    simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8730 (p : Pattern) (guard : d1552 p = 1) : d9 p ≤ (2 : Int) + d1 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8727 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8729 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8731 (p : Pattern) (guard : d0 p = 1) : d21 p ≤ (2 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8732 (p : Pattern) (guard : d1553 p = 1) : d746 p ≤ (2 : Int) + d1 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8730 p hg
    simpa only [d1553, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8731 p hg
    simpa only [d1553, d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8733 (p : Pattern) (guard : d0 p = 1) : d9 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8734 (p : Pattern) (guard : d985 p = 1) : d9 p ≤ (2 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4358 p hg
    simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4429 p hg
    simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8735 (p : Pattern) (guard : d1552 p = 1) : d9 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8733 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8734 p hg
    simpa only [d1552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8736 (p : Pattern) (guard : d1553 p = 1) : d747 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8735 p hg
    simpa only [d1553, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4429 p hg
    simpa only [d1553, d747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8737 (p : Pattern) (guard : d1553 p = 1) : d748 p ≤ (2 : Int) + d1817 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d748, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8732 p hg
    simpa only [d748, d1817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d748, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8736 p hg
    simpa only [d748, d1817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8738 (p : Pattern) (guard : d1553 p = 1) : d749 p ≤ (2 : Int) + d1818 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d749, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8726 p hg
    simpa only [d749, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d749, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8737 p hg
    simpa only [d749, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8739 (p : Pattern) (guard : d1553 p = 1) : d750 p ≤ (2 : Int) + d1819 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d750, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8726 p hg
    simpa only [d750, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d750, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8738 p hg
    simpa only [d750, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8740 (p : Pattern) (guard : d985 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  omega
theorem compare8741 (p : Pattern) (guard : d1552 p = 1) : d17 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1552, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8722 p hg
    simpa only [d1552, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1552, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d1552, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8742 (p : Pattern) (guard : d1553 p = 1) : d19 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8741 p hg
    simpa only [d1553, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4429 p hg
    simpa only [d1553, d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8743 (p : Pattern) (guard : d1553 p = 1) : d751 p ≤ (2 : Int) + d1816 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d751, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8721 p hg
    simpa only [d751, d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d751, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8742 p hg
    simpa only [d751, d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8744 (p : Pattern) (guard : d1552 p = 1) : d21 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1552, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8733 p hg
    simpa only [d1552, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d1552, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8740 p hg
    simpa only [d1552, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8745 (p : Pattern) (guard : d1553 p = 1) : d23 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1552 p = 1 := by simpa only [d1553, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8744 p hg
    simpa only [d1553, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1553, d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4429 p hg
    simpa only [d1553, d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8746 (p : Pattern) (guard : d1553 p = 1) : d752 p ≤ (2 : Int) + d1817 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d752, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8732 p hg
    simpa only [d752, d1817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d752, d1817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8745 p hg
    simpa only [d752, d1817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8747 (p : Pattern) (guard : d1553 p = 1) : d753 p ≤ (2 : Int) + d1818 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d753, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8743 p hg
    simpa only [d753, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d753, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8746 p hg
    simpa only [d753, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8748 (p : Pattern) (guard : d1553 p = 1) : d754 p ≤ (2 : Int) + d1819 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d754, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8743 p hg
    simpa only [d754, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d754, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8747 p hg
    simpa only [d754, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8749 (p : Pattern) (guard : d1553 p = 1) : d755 p ≤ (2 : Int) + d1819 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8739 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8748 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8750 (p : Pattern) (guard : d1553 p = 1) : d756 p ≤ (2 : Int) + d1819 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8739 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8749 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8751 (p : Pattern) (guard : d1553 p = 1) : d757 p ≤ (2 : Int) + d1819 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8749 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8748 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8752 (p : Pattern) (guard : d1553 p = 1) : d758 p ≤ (2 : Int) + d1819 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8750 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8751 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8753 (p : Pattern) (guard : d1553 p = 1) : d759 p ≤ (2 : Int) + d1818 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8738 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8747 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8754 (p : Pattern) (guard : d1553 p = 1) : d760 p ≤ (2 : Int) + d1818 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8738 p hg
    simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8753 p hg
    simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8755 (p : Pattern) (guard : d1553 p = 1) : d761 p ≤ (2 : Int) + d1818 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8753 p hg
    simpa only [d761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8747 p hg
    simpa only [d761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8756 (p : Pattern) (guard : d1553 p = 1) : d762 p ≤ (2 : Int) + d1818 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8754 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8755 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8757 (p : Pattern) (guard : d1553 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  omega
theorem compare8758 (p : Pattern) (guard : d1553 p = 1) : d763 p ≤ (2 : Int) + d1820 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d763, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8726 p hg
    simpa only [d763, d1820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d763, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8757 p hg
    simpa only [d763, d1820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8759 (p : Pattern) (guard : d1553 p = 1) : d764 p ≤ (2 : Int) + d1821 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d764, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8738 p hg
    simpa only [d764, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d764, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8758 p hg
    simpa only [d764, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8760 (p : Pattern) (guard : d1553 p = 1) : d765 p ≤ (2 : Int) + d1820 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d765, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8743 p hg
    simpa only [d765, d1820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d765, d1820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8757 p hg
    simpa only [d765, d1820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8761 (p : Pattern) (guard : d1553 p = 1) : d766 p ≤ (2 : Int) + d1821 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d766, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8747 p hg
    simpa only [d766, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d766, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8760 p hg
    simpa only [d766, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8762 (p : Pattern) (guard : d1553 p = 1) : d767 p ≤ (2 : Int) + d1821 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8759 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8761 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8763 (p : Pattern) (guard : d1553 p = 1) : d768 p ≤ (2 : Int) + d1821 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8759 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8762 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8764 (p : Pattern) (guard : d1553 p = 1) : d769 p ≤ (2 : Int) + d1821 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8762 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8761 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8765 (p : Pattern) (guard : d1553 p = 1) : d770 p ≤ (2 : Int) + d1821 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8763 p hg
    simpa only [d770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8764 p hg
    simpa only [d770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8766 (p : Pattern) (guard : d1553 p = 1) : d771 p ≤ (2 : Int) + d1822 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d771, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8756 p hg
    simpa only [d771, d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d771, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8765 p hg
    simpa only [d771, d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8767 (p : Pattern) (guard : d1553 p = 1) : d772 p ≤ (2 : Int) + d1823 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d772, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8752 p hg
    simpa only [d772, d1823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d772, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8766 p hg
    simpa only [d772, d1823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8768 (p : Pattern) (guard : d1553 p = 1) : d773 p ≤ (2 : Int) + d1824 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d773, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8746 p hg
    simpa only [d773, d1824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d773, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8757 p hg
    simpa only [d773, d1824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8769 (p : Pattern) (guard : d1553 p = 1) : d774 p ≤ (2 : Int) + d1825 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d774, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8746 p hg
    simpa only [d774, d1825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d774, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8768 p hg
    simpa only [d774, d1825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8770 (p : Pattern) (guard : d1553 p = 1) : d775 p ≤ (2 : Int) + d1826 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d775, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8749 p hg
    simpa only [d775, d1826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d775, d1826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8769 p hg
    simpa only [d775, d1826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8771 (p : Pattern) (guard : d1553 p = 1) : d776 p ≤ (2 : Int) + d1827 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d776, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8750 p hg
    simpa only [d776, d1827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d776, d1827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8770 p hg
    simpa only [d776, d1827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8772 (p : Pattern) (guard : d1553 p = 1) : d777 p ≤ (2 : Int) + d1828 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d777, d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8749 p hg
    simpa only [d777, d1828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d777, d1828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8768 p hg
    simpa only [d777, d1828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8773 (p : Pattern) (guard : d1553 p = 1) : d778 p ≤ (2 : Int) + d1829 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d778, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8750 p hg
    simpa only [d778, d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d778, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8772 p hg
    simpa only [d778, d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8774 (p : Pattern) (guard : d1553 p = 1) : d779 p ≤ (2 : Int) + d1830 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d779, d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8771 p hg
    simpa only [d779, d1830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d779, d1830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8773 p hg
    simpa only [d779, d1830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8775 (p : Pattern) (guard : d1553 p = 1) : d780 p ≤ (2 : Int) + d1831 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d780, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8753 p hg
    simpa only [d780, d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d780, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8768 p hg
    simpa only [d780, d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8776 (p : Pattern) (guard : d1553 p = 1) : d781 p ≤ (2 : Int) + d1832 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d781, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8754 p hg
    simpa only [d781, d1832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d781, d1832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8775 p hg
    simpa only [d781, d1832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8777 (p : Pattern) (guard : d1553 p = 1) : d782 p ≤ (2 : Int) + d1833 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d782, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8762 p hg
    simpa only [d782, d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d782, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8768 p hg
    simpa only [d782, d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8778 (p : Pattern) (guard : d1553 p = 1) : d783 p ≤ (2 : Int) + d1834 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d783, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8763 p hg
    simpa only [d783, d1834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d783, d1834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8777 p hg
    simpa only [d783, d1834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8779 (p : Pattern) (guard : d1553 p = 1) : d784 p ≤ (2 : Int) + d1835 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d784, d1835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8776 p hg
    simpa only [d784, d1835, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d784, d1835, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8778 p hg
    simpa only [d784, d1835, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8780 (p : Pattern) (guard : d1553 p = 1) : d785 p ≤ (2 : Int) + d1836 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d785, d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8774 p hg
    simpa only [d785, d1836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d785, d1836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8779 p hg
    simpa only [d785, d1836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8781 (p : Pattern) (guard : d1553 p = 1) : d786 p ≤ (2 : Int) + d1837 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d786, d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8767 p hg
    simpa only [d786, d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d786, d1837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8780 p hg
    simpa only [d786, d1837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8782 (p : Pattern) (guard : d1553 p = 1) : d787 p ≤ (2 : Int) + d1838 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d787, d1838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8726 p hg
    simpa only [d787, d1838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d787, d1838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8758 p hg
    simpa only [d787, d1838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8783 (p : Pattern) (guard : d1553 p = 1) : d788 p ≤ (2 : Int) + d1838 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d788, d1838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8743 p hg
    simpa only [d788, d1838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d788, d1838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8760 p hg
    simpa only [d788, d1838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8784 (p : Pattern) (guard : d1553 p = 1) : d789 p ≤ (2 : Int) + d1838 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8782 p hg
    simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8783 p hg
    simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8785 (p : Pattern) (guard : d1553 p = 1) : d790 p ≤ (2 : Int) + d1838 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8782 p hg
    simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8784 p hg
    simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8786 (p : Pattern) (guard : d1553 p = 1) : d791 p ≤ (2 : Int) + d1838 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8784 p hg
    simpa only [d791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8783 p hg
    simpa only [d791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8787 (p : Pattern) (guard : d1553 p = 1) : d792 p ≤ (2 : Int) + d1838 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8785 p hg
    simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8786 p hg
    simpa only [d792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8788 (p : Pattern) (guard : d1553 p = 1) : d793 p ≤ (2 : Int) + d1839 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d793, d1839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8752 p hg
    simpa only [d793, d1839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d793, d1839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8787 p hg
    simpa only [d793, d1839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8789 (p : Pattern) (guard : d1553 p = 1) : d794 p ≤ (2 : Int) + d1824 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d794, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8737 p hg
    simpa only [d794, d1824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d794, d1824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8757 p hg
    simpa only [d794, d1824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8790 (p : Pattern) (guard : d1553 p = 1) : d795 p ≤ (2 : Int) + d1825 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d795, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8737 p hg
    simpa only [d795, d1825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d795, d1825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8789 p hg
    simpa only [d795, d1825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8791 (p : Pattern) (guard : d1553 p = 1) : d796 p ≤ (2 : Int) + d1825 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8790 p hg
    simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8769 p hg
    simpa only [d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8792 (p : Pattern) (guard : d1553 p = 1) : d797 p ≤ (2 : Int) + d1825 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8790 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8791 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8793 (p : Pattern) (guard : d1553 p = 1) : d798 p ≤ (2 : Int) + d1825 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8791 p hg
    simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8769 p hg
    simpa only [d798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8794 (p : Pattern) (guard : d1553 p = 1) : d799 p ≤ (2 : Int) + d1825 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8792 p hg
    simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8793 p hg
    simpa only [d799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8795 (p : Pattern) (guard : d1553 p = 1) : d800 p ≤ (2 : Int) + d1840 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d800, d1840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8788 p hg
    simpa only [d800, d1840, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d800, d1840, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8794 p hg
    simpa only [d800, d1840, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8796 (p : Pattern) (guard : d1553 p = 1) : d801 p ≤ (2 : Int) + d1841 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d801, d1841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8784 p hg
    simpa only [d801, d1841, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d801, d1841, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8768 p hg
    simpa only [d801, d1841, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8797 (p : Pattern) (guard : d1553 p = 1) : d802 p ≤ (2 : Int) + d1842 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d802, d1842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8785 p hg
    simpa only [d802, d1842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d802, d1842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8796 p hg
    simpa only [d802, d1842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8798 (p : Pattern) (guard : d1553 p = 1) : d803 p ≤ (2 : Int) + d1843 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d803, d1843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8773 p hg
    simpa only [d803, d1843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d803, d1843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8797 p hg
    simpa only [d803, d1843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8799 (p : Pattern) (guard : d1553 p = 1) : d804 p ≤ (2 : Int) + d1844 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d804, d1844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8791 p hg
    simpa only [d804, d1844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d804, d1844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8757 p hg
    simpa only [d804, d1844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8800 (p : Pattern) (guard : d1553 p = 1) : d805 p ≤ (2 : Int) + d1845 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d805, d1845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8792 p hg
    simpa only [d805, d1845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d805, d1845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8799 p hg
    simpa only [d805, d1845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8801 (p : Pattern) (guard : d1553 p = 1) : d806 p ≤ (2 : Int) + d1824 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8789 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8768 p hg
    simpa only [d806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8802 (p : Pattern) (guard : d1553 p = 1) : d807 p ≤ (2 : Int) + d1824 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8789 p hg
    simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8801 p hg
    simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8803 (p : Pattern) (guard : d1553 p = 1) : d808 p ≤ (2 : Int) + d1846 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d808, d1846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8801 p hg
    simpa only [d808, d1846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d808, d1846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8757 p hg
    simpa only [d808, d1846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8804 (p : Pattern) (guard : d1553 p = 1) : d809 p ≤ (2 : Int) + d1847 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d809, d1847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8802 p hg
    simpa only [d809, d1847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d809, d1847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8803 p hg
    simpa only [d809, d1847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8805 (p : Pattern) (guard : d1553 p = 1) : d810 p ≤ (2 : Int) + d1848 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d810, d1848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8800 p hg
    simpa only [d810, d1848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d810, d1848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8804 p hg
    simpa only [d810, d1848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8806 (p : Pattern) (guard : d1553 p = 1) : d811 p ≤ (2 : Int) + d1849 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d811, d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8798 p hg
    simpa only [d811, d1849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d811, d1849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8805 p hg
    simpa only [d811, d1849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8807 (p : Pattern) (guard : d1553 p = 1) : d812 p ≤ (2 : Int) + d1850 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d812, d1850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8795 p hg
    simpa only [d812, d1850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d812, d1850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8806 p hg
    simpa only [d812, d1850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8808 (p : Pattern) (guard : d1553 p = 1) : d813 p ≤ (2 : Int) + d1851 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d813, d1851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8781 p hg
    simpa only [d813, d1851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d813, d1851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8807 p hg
    simpa only [d813, d1851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8809 (p : Pattern) (guard : d1553 p = 1) : d814 p ≤ (2 : Int) + d1852 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d814, d1852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8773 p hg
    simpa only [d814, d1852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d814, d1852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8779 p hg
    simpa only [d814, d1852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8810 (p : Pattern) (guard : d1553 p = 1) : d815 p ≤ (2 : Int) + d1853 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d815, d1853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8767 p hg
    simpa only [d815, d1853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d815, d1853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8809 p hg
    simpa only [d815, d1853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8811 (p : Pattern) (guard : d1553 p = 1) : d816 p ≤ (2 : Int) + d1824 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8801 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8768 p hg
    simpa only [d816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8812 (p : Pattern) (guard : d1553 p = 1) : d817 p ≤ (2 : Int) + d1824 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8802 p hg
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8811 p hg
    simpa only [d817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8813 (p : Pattern) (guard : d1553 p = 1) : d818 p ≤ (2 : Int) + d1854 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d818, d1854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8794 p hg
    simpa only [d818, d1854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d818, d1854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8812 p hg
    simpa only [d818, d1854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8814 (p : Pattern) (guard : d1553 p = 1) : d819 p ≤ (2 : Int) + d1855 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d819, d1855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8788 p hg
    simpa only [d819, d1855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d819, d1855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8813 p hg
    simpa only [d819, d1855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8815 (p : Pattern) (guard : d1553 p = 1) : d820 p ≤ (2 : Int) + d1856 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d820, d1856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8773 p hg
    simpa only [d820, d1856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d820, d1856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8778 p hg
    simpa only [d820, d1856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8816 (p : Pattern) (guard : d1553 p = 1) : d821 p ≤ (2 : Int) + d1857 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d821, d1857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8804 p hg
    simpa only [d821, d1857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d821, d1857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8757 p hg
    simpa only [d821, d1857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8817 (p : Pattern) (guard : d1553 p = 1) : d822 p ≤ (2 : Int) + d1858 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d822, d1858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8815 p hg
    simpa only [d822, d1858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d822, d1858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8816 p hg
    simpa only [d822, d1858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8818 (p : Pattern) (guard : d1553 p = 1) : d823 p ≤ (2 : Int) + d1859 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d823, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8814 p hg
    simpa only [d823, d1859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d823, d1859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8817 p hg
    simpa only [d823, d1859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8819 (p : Pattern) (guard : d1553 p = 1) : d824 p ≤ (2 : Int) + d1860 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d824, d1860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8810 p hg
    simpa only [d824, d1860, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d824, d1860, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8818 p hg
    simpa only [d824, d1860, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
