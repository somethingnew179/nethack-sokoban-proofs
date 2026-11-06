/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons062
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8820 (p : Pattern) (guard : d1553 p = 1) : d825 p ≤ (2 : Int) + d1861 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1553 p = 1 := by simpa only [d825, d1861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8808 p hg
    simpa only [d825, d1861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1553 p = 1 := by simpa only [d825, d1861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8819 p hg
    simpa only [d825, d1861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8821 (p : Pattern) (guard : d0 p = 1) : d750 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8822 (p : Pattern) (guard : d1249 p = 1) : d750 p ≤ (0 : Int) + d328 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8377 p hg
    simpa only [d1249, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8821 p hg
    simpa only [d1249, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8823 (p : Pattern) (guard : d0 p = 1) : d754 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8824 (p : Pattern) (guard : d1249 p = 1) : d755 p ≤ (0 : Int) + d328 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d755, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8377 p hg
    simpa only [d1249, d755, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d755, d328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8823 p hg
    simpa only [d1249, d755, d328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8825 (p : Pattern) (guard : d1249 p = 1) : d756 p ≤ (0 : Int) + d328 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8822 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8824 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8826 (p : Pattern) (guard : d1249 p = 1) : d754 p ≤ (0 : Int) + d329 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8399 p hg
    simpa only [d1249, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8823 p hg
    simpa only [d1249, d329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8827 (p : Pattern) (guard : d1249 p = 1) : d757 p ≤ (0 : Int) + d330 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d757, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8824 p hg
    simpa only [d757, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d757, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8826 p hg
    simpa only [d757, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8828 (p : Pattern) (guard : d1249 p = 1) : d758 p ≤ (0 : Int) + d331 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d758, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8825 p hg
    simpa only [d758, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d758, d331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8827 p hg
    simpa only [d758, d331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8829 (p : Pattern) (guard : d0 p = 1) : d749 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8830 (p : Pattern) (guard : d1249 p = 1) : d749 p ≤ (0 : Int) + d332 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8376 p hg
    simpa only [d1249, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8829 p hg
    simpa only [d1249, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8831 (p : Pattern) (guard : d0 p = 1) : d753 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8832 (p : Pattern) (guard : d1249 p = 1) : d759 p ≤ (0 : Int) + d332 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d759, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8376 p hg
    simpa only [d1249, d759, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d759, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8831 p hg
    simpa only [d1249, d759, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8833 (p : Pattern) (guard : d1249 p = 1) : d760 p ≤ (0 : Int) + d332 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8830 p hg
    simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8832 p hg
    simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8834 (p : Pattern) (guard : d1249 p = 1) : d753 p ≤ (0 : Int) + d333 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8398 p hg
    simpa only [d1249, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8831 p hg
    simpa only [d1249, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8835 (p : Pattern) (guard : d1249 p = 1) : d761 p ≤ (0 : Int) + d334 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d761, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8832 p hg
    simpa only [d761, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d761, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8834 p hg
    simpa only [d761, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8836 (p : Pattern) (guard : d1249 p = 1) : d762 p ≤ (0 : Int) + d335 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d762, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8833 p hg
    simpa only [d762, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d762, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8835 p hg
    simpa only [d762, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8837 (p : Pattern) (guard : d0 p = 1) : d764 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8838 (p : Pattern) (guard : d1249 p = 1) : d764 p ≤ (0 : Int) + d336 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8410 p hg
    simpa only [d1249, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8837 p hg
    simpa only [d1249, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8839 (p : Pattern) (guard : d0 p = 1) : d766 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8840 (p : Pattern) (guard : d1249 p = 1) : d767 p ≤ (0 : Int) + d336 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d767, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8410 p hg
    simpa only [d1249, d767, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d767, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8839 p hg
    simpa only [d1249, d767, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8841 (p : Pattern) (guard : d1249 p = 1) : d768 p ≤ (0 : Int) + d336 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8838 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8840 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8842 (p : Pattern) (guard : d1249 p = 1) : d766 p ≤ (0 : Int) + d337 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8419 p hg
    simpa only [d1249, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8839 p hg
    simpa only [d1249, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8843 (p : Pattern) (guard : d1249 p = 1) : d769 p ≤ (0 : Int) + d338 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d769, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8840 p hg
    simpa only [d769, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d769, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8842 p hg
    simpa only [d769, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8844 (p : Pattern) (guard : d1249 p = 1) : d770 p ≤ (0 : Int) + d339 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d770, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8841 p hg
    simpa only [d770, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d770, d339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8843 p hg
    simpa only [d770, d339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8845 (p : Pattern) (guard : d1249 p = 1) : d771 p ≤ (0 : Int) + d340 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d771, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8836 p hg
    simpa only [d771, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d771, d340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8844 p hg
    simpa only [d771, d340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8846 (p : Pattern) (guard : d1249 p = 1) : d772 p ≤ (0 : Int) + d341 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d772, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8828 p hg
    simpa only [d772, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d772, d341, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8845 p hg
    simpa only [d772, d341, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8847 (p : Pattern) (guard : d0 p = 1) : d774 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8848 (p : Pattern) (guard : d1249 p = 1) : d774 p ≤ (0 : Int) + d342 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8426 p hg
    simpa only [d1249, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8847 p hg
    simpa only [d1249, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8849 (p : Pattern) (guard : d1249 p = 1) : d775 p ≤ (0 : Int) + d343 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d775, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8824 p hg
    simpa only [d775, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d775, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8848 p hg
    simpa only [d775, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8850 (p : Pattern) (guard : d1249 p = 1) : d776 p ≤ (0 : Int) + d344 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d776, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8825 p hg
    simpa only [d776, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d776, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8849 p hg
    simpa only [d776, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8851 (p : Pattern) (guard : d0 p = 1) : d773 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8852 (p : Pattern) (guard : d1249 p = 1) : d773 p ≤ (0 : Int) + d345 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8425 p hg
    simpa only [d1249, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8851 p hg
    simpa only [d1249, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8853 (p : Pattern) (guard : d1249 p = 1) : d777 p ≤ (0 : Int) + d346 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d777, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8824 p hg
    simpa only [d777, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d777, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8852 p hg
    simpa only [d777, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8854 (p : Pattern) (guard : d1249 p = 1) : d778 p ≤ (0 : Int) + d347 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d778, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8825 p hg
    simpa only [d778, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d778, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8853 p hg
    simpa only [d778, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8855 (p : Pattern) (guard : d1249 p = 1) : d779 p ≤ (0 : Int) + d348 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d779, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8850 p hg
    simpa only [d779, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d779, d348, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8854 p hg
    simpa only [d779, d348, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8856 (p : Pattern) (guard : d1249 p = 1) : d780 p ≤ (0 : Int) + d349 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d780, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8832 p hg
    simpa only [d780, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d780, d349, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8852 p hg
    simpa only [d780, d349, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8857 (p : Pattern) (guard : d1249 p = 1) : d781 p ≤ (0 : Int) + d350 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d781, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8833 p hg
    simpa only [d781, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d781, d350, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8856 p hg
    simpa only [d781, d350, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8858 (p : Pattern) (guard : d1249 p = 1) : d782 p ≤ (0 : Int) + d351 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d782, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8840 p hg
    simpa only [d782, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d782, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8852 p hg
    simpa only [d782, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8859 (p : Pattern) (guard : d1249 p = 1) : d783 p ≤ (0 : Int) + d352 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d783, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8841 p hg
    simpa only [d783, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d783, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8858 p hg
    simpa only [d783, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8860 (p : Pattern) (guard : d1249 p = 1) : d784 p ≤ (0 : Int) + d353 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d784, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8857 p hg
    simpa only [d784, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d784, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8859 p hg
    simpa only [d784, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8861 (p : Pattern) (guard : d1249 p = 1) : d785 p ≤ (0 : Int) + d354 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d785, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8855 p hg
    simpa only [d785, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d785, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8860 p hg
    simpa only [d785, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8862 (p : Pattern) (guard : d1249 p = 1) : d786 p ≤ (0 : Int) + d355 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d786, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8846 p hg
    simpa only [d786, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d786, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8861 p hg
    simpa only [d786, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8863 (p : Pattern) (guard : d0 p = 1) : d787 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8864 (p : Pattern) (guard : d1249 p = 1) : d787 p ≤ (0 : Int) + d356 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8443 p hg
    simpa only [d1249, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8863 p hg
    simpa only [d1249, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8865 (p : Pattern) (guard : d0 p = 1) : d788 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8866 (p : Pattern) (guard : d1249 p = 1) : d789 p ≤ (0 : Int) + d356 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d789, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8443 p hg
    simpa only [d1249, d789, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d789, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8865 p hg
    simpa only [d1249, d789, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8867 (p : Pattern) (guard : d1249 p = 1) : d790 p ≤ (0 : Int) + d356 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8864 p hg
    simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8866 p hg
    simpa only [d790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8868 (p : Pattern) (guard : d1249 p = 1) : d788 p ≤ (0 : Int) + d357 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8449 p hg
    simpa only [d1249, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8865 p hg
    simpa only [d1249, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8869 (p : Pattern) (guard : d1249 p = 1) : d791 p ≤ (0 : Int) + d358 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d791, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8866 p hg
    simpa only [d791, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d791, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8868 p hg
    simpa only [d791, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8870 (p : Pattern) (guard : d1249 p = 1) : d792 p ≤ (0 : Int) + d359 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d792, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8867 p hg
    simpa only [d792, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d792, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8869 p hg
    simpa only [d792, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8871 (p : Pattern) (guard : d1249 p = 1) : d793 p ≤ (0 : Int) + d360 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d793, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8828 p hg
    simpa only [d793, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d793, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8870 p hg
    simpa only [d793, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8872 (p : Pattern) (guard : d0 p = 1) : d795 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8873 (p : Pattern) (guard : d1249 p = 1) : d795 p ≤ (0 : Int) + d361 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8455 p hg
    simpa only [d1249, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8872 p hg
    simpa only [d1249, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8874 (p : Pattern) (guard : d1249 p = 1) : d796 p ≤ (0 : Int) + d361 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d796, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8455 p hg
    simpa only [d1249, d796, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d796, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8847 p hg
    simpa only [d1249, d796, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8875 (p : Pattern) (guard : d1249 p = 1) : d797 p ≤ (0 : Int) + d361 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8873 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8874 p hg
    simpa only [d797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8876 (p : Pattern) (guard : d1249 p = 1) : d798 p ≤ (0 : Int) + d362 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d798, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8874 p hg
    simpa only [d798, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d798, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8848 p hg
    simpa only [d798, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8877 (p : Pattern) (guard : d1249 p = 1) : d799 p ≤ (0 : Int) + d363 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d799, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8875 p hg
    simpa only [d799, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d799, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8876 p hg
    simpa only [d799, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8878 (p : Pattern) (guard : d1249 p = 1) : d800 p ≤ (0 : Int) + d364 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d800, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8871 p hg
    simpa only [d800, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d800, d364, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8877 p hg
    simpa only [d800, d364, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8879 (p : Pattern) (guard : d1249 p = 1) : d801 p ≤ (0 : Int) + d365 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d801, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8866 p hg
    simpa only [d801, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d801, d365, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8852 p hg
    simpa only [d801, d365, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8880 (p : Pattern) (guard : d1249 p = 1) : d802 p ≤ (0 : Int) + d366 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d802, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8867 p hg
    simpa only [d802, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d802, d366, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8879 p hg
    simpa only [d802, d366, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8881 (p : Pattern) (guard : d1249 p = 1) : d803 p ≤ (0 : Int) + d367 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d803, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8854 p hg
    simpa only [d803, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d803, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8880 p hg
    simpa only [d803, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8882 (p : Pattern) (guard : d1249 p = 1) : d804 p ≤ (0 : Int) + d368 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d804, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8874 p hg
    simpa only [d804, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d804, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4070 p hg
    simpa only [d804, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8883 (p : Pattern) (guard : d1249 p = 1) : d805 p ≤ (0 : Int) + d369 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d805, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8875 p hg
    simpa only [d805, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d805, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8882 p hg
    simpa only [d805, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8884 (p : Pattern) (guard : d0 p = 1) : d794 p ≤ (0 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8885 (p : Pattern) (guard : d1249 p = 1) : d794 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8454 p hg
    simpa only [d1249, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8884 p hg
    simpa only [d1249, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8886 (p : Pattern) (guard : d1249 p = 1) : d806 p ≤ (0 : Int) + d370 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1249, d806, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8454 p hg
    simpa only [d1249, d806, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1249, d806, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8851 p hg
    simpa only [d1249, d806, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8887 (p : Pattern) (guard : d1249 p = 1) : d807 p ≤ (0 : Int) + d370 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8885 p hg
    simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8886 p hg
    simpa only [d807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8888 (p : Pattern) (guard : d1249 p = 1) : d808 p ≤ (0 : Int) + d371 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d808, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8886 p hg
    simpa only [d808, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d808, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4070 p hg
    simpa only [d808, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8889 (p : Pattern) (guard : d1249 p = 1) : d809 p ≤ (0 : Int) + d372 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d809, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8887 p hg
    simpa only [d809, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d809, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8888 p hg
    simpa only [d809, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8890 (p : Pattern) (guard : d1249 p = 1) : d810 p ≤ (0 : Int) + d373 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d810, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8883 p hg
    simpa only [d810, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d810, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8889 p hg
    simpa only [d810, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8891 (p : Pattern) (guard : d1249 p = 1) : d811 p ≤ (0 : Int) + d374 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d811, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8881 p hg
    simpa only [d811, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d811, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8890 p hg
    simpa only [d811, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8892 (p : Pattern) (guard : d1249 p = 1) : d812 p ≤ (0 : Int) + d375 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d812, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8878 p hg
    simpa only [d812, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d812, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8891 p hg
    simpa only [d812, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8893 (p : Pattern) (guard : d1249 p = 1) : d813 p ≤ (0 : Int) + d376 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d813, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8862 p hg
    simpa only [d813, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d813, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8892 p hg
    simpa only [d813, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8894 (p : Pattern) (guard : d1249 p = 1) : d814 p ≤ (0 : Int) + d377 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d814, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8854 p hg
    simpa only [d814, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d814, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8860 p hg
    simpa only [d814, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8895 (p : Pattern) (guard : d1249 p = 1) : d815 p ≤ (0 : Int) + d378 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d815, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8846 p hg
    simpa only [d815, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d815, d378, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8894 p hg
    simpa only [d815, d378, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8896 (p : Pattern) (guard : d1249 p = 1) : d816 p ≤ (0 : Int) + d379 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d816, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8886 p hg
    simpa only [d816, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d816, d379, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8852 p hg
    simpa only [d816, d379, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8897 (p : Pattern) (guard : d1249 p = 1) : d817 p ≤ (0 : Int) + d380 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d817, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8887 p hg
    simpa only [d817, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d817, d380, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8896 p hg
    simpa only [d817, d380, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8898 (p : Pattern) (guard : d1249 p = 1) : d818 p ≤ (0 : Int) + d381 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d818, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8877 p hg
    simpa only [d818, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d818, d381, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8897 p hg
    simpa only [d818, d381, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8899 (p : Pattern) (guard : d1249 p = 1) : d819 p ≤ (0 : Int) + d382 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d819, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8871 p hg
    simpa only [d819, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d819, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8898 p hg
    simpa only [d819, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8900 (p : Pattern) (guard : d1249 p = 1) : d820 p ≤ (0 : Int) + d383 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d820, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8854 p hg
    simpa only [d820, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d820, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8859 p hg
    simpa only [d820, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8901 (p : Pattern) (guard : d1249 p = 1) : d821 p ≤ (0 : Int) + d384 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d821, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8889 p hg
    simpa only [d821, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d821, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4070 p hg
    simpa only [d821, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8902 (p : Pattern) (guard : d1249 p = 1) : d822 p ≤ (0 : Int) + d385 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d822, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8900 p hg
    simpa only [d822, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d822, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8901 p hg
    simpa only [d822, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8903 (p : Pattern) (guard : d1249 p = 1) : d823 p ≤ (0 : Int) + d386 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d823, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8899 p hg
    simpa only [d823, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d823, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8902 p hg
    simpa only [d823, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8904 (p : Pattern) (guard : d1249 p = 1) : d824 p ≤ (0 : Int) + d387 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d824, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8895 p hg
    simpa only [d824, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d824, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8903 p hg
    simpa only [d824, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8905 (p : Pattern) (guard : d1249 p = 1) : d825 p ≤ (0 : Int) + d388 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1249 p = 1 := by simpa only [d825, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8893 p hg
    simpa only [d825, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1249 p = 1 := by simpa only [d825, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8904 p hg
    simpa only [d825, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8906 (p : Pattern) (guard : d1 p = 1) : d134 p ≤ (5 : Int) + d134 p := by
  omega
theorem compare8907 (p : Pattern) (guard : d29 p = 1) : d0 p ≤ (2 : Int) + d0 p := by
  omega
theorem compare8908 (p : Pattern) (guard : d1690 p = 1) : d4 p ≤ (2 : Int) + d0 p := by
  cases selected : p 160 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d1690, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8907 p hg
    simpa only [d1690, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1690, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8716 p hg
    simpa only [d1690, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8909 (p : Pattern) (guard : d29 p = 1) : d0 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) ≤ (2 : Int) + 2
  decide
theorem compare8910 (p : Pattern) (guard : d1690 p = 1) : d5 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d1690, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8909 p hg
    simpa only [d1690, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1690, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4429 p hg
    simpa only [d1690, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8911 (p : Pattern) (guard : d1690 p = 1) : d6 p ≤ (2 : Int) + d1554 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d6, d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8908 p hg
    simpa only [d6, d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d6, d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8910 p hg
    simpa only [d6, d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8912 (p : Pattern) (guard : d1690 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  omega
theorem compare8913 (p : Pattern) (guard : d1690 p = 1) : d7 p ≤ (2 : Int) + d1554 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d7, d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8908 p hg
    simpa only [d7, d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d7, d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d7, d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8914 (p : Pattern) (guard : d1690 p = 1) : d8 p ≤ (2 : Int) + d1554 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8911 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8913 p hg
    simpa only [d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8915 (p : Pattern) (guard : d29 p = 1) : d1 p ≤ (2 : Int) + d1 p := by
  omega
theorem compare8916 (p : Pattern) (guard : d1690 p = 1) : d10 p ≤ (2 : Int) + d1 p := by
  cases selected : p 160 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d1690, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8915 p hg
    simpa only [d1690, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1690, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8727 p hg
    simpa only [d1690, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8917 (p : Pattern) (guard : d29 p = 1) : d1 p ≤ (2 : Int) + d2 p := by
  change (1 : Int) ≤ (2 : Int) + 2
  decide
theorem compare8918 (p : Pattern) (guard : d1690 p = 1) : d11 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d1690, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8917 p hg
    simpa only [d1690, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1690, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4429 p hg
    simpa only [d1690, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8919 (p : Pattern) (guard : d1690 p = 1) : d12 p ≤ (2 : Int) + d1556 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d12, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8916 p hg
    simpa only [d12, d1556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d12, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8918 p hg
    simpa only [d12, d1556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8920 (p : Pattern) (guard : d1690 p = 1) : d13 p ≤ (2 : Int) + d1556 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d13, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8916 p hg
    simpa only [d13, d1556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d13, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d13, d1556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8921 (p : Pattern) (guard : d1690 p = 1) : d14 p ≤ (2 : Int) + d1556 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8919 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8920 p hg
    simpa only [d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8922 (p : Pattern) (guard : d1690 p = 1) : d15 p ≤ (2 : Int) + d1862 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d15, d1862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8914 p hg
    simpa only [d15, d1862, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d15, d1862, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8921 p hg
    simpa only [d15, d1862, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8923 (p : Pattern) (guard : d1690 p = 1) : d16 p ≤ (2 : Int) + d1863 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d16, d1863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8914 p hg
    simpa only [d16, d1863, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d16, d1863, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8922 p hg
    simpa only [d16, d1863, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8924 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8925 (p : Pattern) (guard : d29 p = 1) : d3 p ≤ (2 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8924 p hg
    simpa only [d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d29, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8926 (p : Pattern) (guard : d1690 p = 1) : d17 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d1690, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8925 p hg
    simpa only [d1690, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1690, d17, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4429 p hg
    simpa only [d1690, d17, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8927 (p : Pattern) (guard : d1690 p = 1) : d18 p ≤ (2 : Int) + d1554 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d18, d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8908 p hg
    simpa only [d18, d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d18, d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8926 p hg
    simpa only [d18, d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8928 (p : Pattern) (guard : d1690 p = 1) : d19 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8926 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8929 (p : Pattern) (guard : d1690 p = 1) : d20 p ≤ (2 : Int) + d1864 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d20, d1864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8927 p hg
    simpa only [d20, d1864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d20, d1864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8928 p hg
    simpa only [d20, d1864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8930 (p : Pattern) (guard : d0 p = 1) : d1 p ≤ (2 : Int) + d2 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8931 (p : Pattern) (guard : d29 p = 1) : d9 p ≤ (2 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d29, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8930 p hg
    simpa only [d29, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4310 p hg
    simpa only [d29, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8932 (p : Pattern) (guard : d1690 p = 1) : d21 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d1690, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8931 p hg
    simpa only [d1690, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1690, d21, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4429 p hg
    simpa only [d1690, d21, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8933 (p : Pattern) (guard : d1690 p = 1) : d22 p ≤ (2 : Int) + d1556 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d22, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8916 p hg
    simpa only [d22, d1556, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d22, d1556, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8932 p hg
    simpa only [d22, d1556, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8934 (p : Pattern) (guard : d1690 p = 1) : d23 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8932 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8935 (p : Pattern) (guard : d1690 p = 1) : d24 p ≤ (2 : Int) + d1865 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d24, d1865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8933 p hg
    simpa only [d24, d1865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d24, d1865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8934 p hg
    simpa only [d24, d1865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8936 (p : Pattern) (guard : d1690 p = 1) : d25 p ≤ (2 : Int) + d1866 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d25, d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8929 p hg
    simpa only [d25, d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d25, d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8935 p hg
    simpa only [d25, d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8937 (p : Pattern) (guard : d1690 p = 1) : d26 p ≤ (2 : Int) + d1867 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d26, d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8929 p hg
    simpa only [d26, d1867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d26, d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8936 p hg
    simpa only [d26, d1867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8938 (p : Pattern) (guard : d1690 p = 1) : d27 p ≤ (2 : Int) + d1868 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d27, d1868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8923 p hg
    simpa only [d27, d1868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d27, d1868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8937 p hg
    simpa only [d27, d1868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8939 (p : Pattern) (guard : d1690 p = 1) : d28 p ≤ (2 : Int) + d1869 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d28, d1869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8923 p hg
    simpa only [d28, d1869, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d28, d1869, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8938 p hg
    simpa only [d28, d1869, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8940 (p : Pattern) (guard : d29 p = 1) : d29 p ≤ (2 : Int) + d2 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8924 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4358 p hg
    simpa only [d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8941 (p : Pattern) (guard : d1690 p = 1) : d30 p ≤ (2 : Int) + d2 p := by
  cases selected : p 160 with
  | false =>
    have hg : d29 p = 1 := by simpa only [d1690, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8940 p hg
    simpa only [d1690, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1690, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4429 p hg
    simpa only [d1690, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8942 (p : Pattern) (guard : d1690 p = 1) : d31 p ≤ (2 : Int) + d1554 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d31, d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8908 p hg
    simpa only [d31, d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d31, d1554, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8941 p hg
    simpa only [d31, d1554, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8943 (p : Pattern) (guard : d1690 p = 1) : d32 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8941 p hg
    simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8944 (p : Pattern) (guard : d1690 p = 1) : d33 p ≤ (2 : Int) + d1864 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d33, d1864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8942 p hg
    simpa only [d33, d1864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d33, d1864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8943 p hg
    simpa only [d33, d1864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8945 (p : Pattern) (guard : d1690 p = 1) : d34 p ≤ (2 : Int) + d1866 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d34, d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8944 p hg
    simpa only [d34, d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d34, d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8935 p hg
    simpa only [d34, d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8946 (p : Pattern) (guard : d1690 p = 1) : d35 p ≤ (2 : Int) + d1867 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d35, d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8944 p hg
    simpa only [d35, d1867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d35, d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8945 p hg
    simpa only [d35, d1867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8947 (p : Pattern) (guard : d1690 p = 1) : d36 p ≤ (2 : Int) + d1868 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d36, d1868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8923 p hg
    simpa only [d36, d1868, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d36, d1868, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8946 p hg
    simpa only [d36, d1868, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8948 (p : Pattern) (guard : d1690 p = 1) : d37 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8910 p hg
    simpa only [d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8949 (p : Pattern) (guard : d1690 p = 1) : d38 p ≤ (2 : Int) + d1864 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d38, d1864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8911 p hg
    simpa only [d38, d1864, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d38, d1864, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8948 p hg
    simpa only [d38, d1864, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8950 (p : Pattern) (guard : d1690 p = 1) : d39 p ≤ (2 : Int) + d2 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8918 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8912 p hg
    simpa only [d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8951 (p : Pattern) (guard : d1690 p = 1) : d40 p ≤ (2 : Int) + d1865 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d40, d1865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8919 p hg
    simpa only [d40, d1865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d40, d1865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8950 p hg
    simpa only [d40, d1865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8952 (p : Pattern) (guard : d1690 p = 1) : d41 p ≤ (2 : Int) + d1866 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d41, d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8949 p hg
    simpa only [d41, d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d41, d1866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8951 p hg
    simpa only [d41, d1866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8953 (p : Pattern) (guard : d1690 p = 1) : d42 p ≤ (2 : Int) + d1867 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d42, d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8949 p hg
    simpa only [d42, d1867, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d42, d1867, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8952 p hg
    simpa only [d42, d1867, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8954 (p : Pattern) (guard : d1690 p = 1) : d43 p ≤ (2 : Int) + d1867 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8953 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8937 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8955 (p : Pattern) (guard : d1690 p = 1) : d44 p ≤ (2 : Int) + d1870 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d44, d1870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8947 p hg
    simpa only [d44, d1870, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d44, d1870, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8954 p hg
    simpa only [d44, d1870, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8956 (p : Pattern) (guard : d1690 p = 1) : d45 p ≤ (2 : Int) + d1871 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d45, d1871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8939 p hg
    simpa only [d45, d1871, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d45, d1871, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8955 p hg
    simpa only [d45, d1871, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8957 (p : Pattern) (guard : d1690 p = 1) : d46 p ≤ (2 : Int) + d1872 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d46, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8922 p hg
    simpa only [d46, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d46, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8936 p hg
    simpa only [d46, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8958 (p : Pattern) (guard : d1690 p = 1) : d47 p ≤ (2 : Int) + d1873 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d47, d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8922 p hg
    simpa only [d47, d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d47, d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8957 p hg
    simpa only [d47, d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8959 (p : Pattern) (guard : d1690 p = 1) : d48 p ≤ (2 : Int) + d1872 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1690 p = 1 := by simpa only [d48, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8922 p hg
    simpa only [d48, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1690 p = 1 := by simpa only [d48, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8945 p hg
    simpa only [d48, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
