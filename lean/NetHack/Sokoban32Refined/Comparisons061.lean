/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons060
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8540 (p : Pattern) (guard : d985 p = 1) : d757 p ≤ (4 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d757, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8532 p hg
    simpa only [d757, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d757, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8539 p hg
    simpa only [d757, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8541 (p : Pattern) (guard : d985 p = 1) : d758 p ≤ (4 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d758, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8524 p hg
    simpa only [d758, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d758, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8540 p hg
    simpa only [d758, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8542 (p : Pattern) (guard : d985 p = 1) : d759 p ≤ (4 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d759, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8511 p hg
    simpa only [d759, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d759, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8521 p hg
    simpa only [d759, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8543 (p : Pattern) (guard : d985 p = 1) : d760 p ≤ (4 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d760, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8511 p hg
    simpa only [d760, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d760, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8542 p hg
    simpa only [d760, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8544 (p : Pattern) (guard : d985 p = 1) : d759 p ≤ (4 : Int) + d48 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d759, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8511 p hg
    simpa only [d759, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d759, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8530 p hg
    simpa only [d759, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8545 (p : Pattern) (guard : d985 p = 1) : d753 p ≤ (4 : Int) + d49 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8537 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8521 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8546 (p : Pattern) (guard : d985 p = 1) : d761 p ≤ (4 : Int) + d50 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d761, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8544 p hg
    simpa only [d761, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d761, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8545 p hg
    simpa only [d761, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8547 (p : Pattern) (guard : d985 p = 1) : d762 p ≤ (4 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d762, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8543 p hg
    simpa only [d762, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d762, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8546 p hg
    simpa only [d762, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8548 (p : Pattern) (guard : d985 p = 1) : d763 p ≤ (4 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d763, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8501 p hg
    simpa only [d763, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d763, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d763, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8549 (p : Pattern) (guard : d985 p = 1) : d764 p ≤ (4 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d764, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8511 p hg
    simpa only [d764, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d764, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8548 p hg
    simpa only [d764, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8550 (p : Pattern) (guard : d985 p = 1) : d765 p ≤ (4 : Int) + d54 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d765, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8516 p hg
    simpa only [d765, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d765, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d765, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8551 (p : Pattern) (guard : d985 p = 1) : d766 p ≤ (4 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d766, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8521 p hg
    simpa only [d766, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d766, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8550 p hg
    simpa only [d766, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8552 (p : Pattern) (guard : d985 p = 1) : d767 p ≤ (4 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d767, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8549 p hg
    simpa only [d767, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d767, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8551 p hg
    simpa only [d767, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8553 (p : Pattern) (guard : d985 p = 1) : d768 p ≤ (4 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d768, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8549 p hg
    simpa only [d768, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d768, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8552 p hg
    simpa only [d768, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8554 (p : Pattern) (guard : d985 p = 1) : d765 p ≤ (4 : Int) + d58 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d765, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8529 p hg
    simpa only [d765, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d765, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d765, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8555 (p : Pattern) (guard : d985 p = 1) : d766 p ≤ (4 : Int) + d59 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d766, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8530 p hg
    simpa only [d766, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d766, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8554 p hg
    simpa only [d766, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8556 (p : Pattern) (guard : d985 p = 1) : d767 p ≤ (4 : Int) + d60 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d767, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8549 p hg
    simpa only [d767, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d767, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8555 p hg
    simpa only [d767, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8557 (p : Pattern) (guard : d985 p = 1) : d765 p ≤ (4 : Int) + d61 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d765, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8534 p hg
    simpa only [d765, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d765, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d765, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8558 (p : Pattern) (guard : d985 p = 1) : d766 p ≤ (4 : Int) + d62 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d766, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8537 p hg
    simpa only [d766, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d766, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8557 p hg
    simpa only [d766, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8559 (p : Pattern) (guard : d985 p = 1) : d766 p ≤ (4 : Int) + d63 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8558 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8551 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8560 (p : Pattern) (guard : d985 p = 1) : d769 p ≤ (4 : Int) + d64 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d769, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8556 p hg
    simpa only [d769, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d769, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8559 p hg
    simpa only [d769, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8561 (p : Pattern) (guard : d985 p = 1) : d770 p ≤ (4 : Int) + d65 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8553 p hg
    simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8560 p hg
    simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8562 (p : Pattern) (guard : d985 p = 1) : d771 p ≤ (4 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d771, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8547 p hg
    simpa only [d771, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d771, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8561 p hg
    simpa only [d771, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8563 (p : Pattern) (guard : d985 p = 1) : d772 p ≤ (4 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d772, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8541 p hg
    simpa only [d772, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d772, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8562 p hg
    simpa only [d772, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8564 (p : Pattern) (guard : d985 p = 1) : d773 p ≤ (4 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d773, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8536 p hg
    simpa only [d773, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d773, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d773, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8565 (p : Pattern) (guard : d985 p = 1) : d774 p ≤ (4 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d774, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8536 p hg
    simpa only [d774, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d774, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8564 p hg
    simpa only [d774, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8566 (p : Pattern) (guard : d985 p = 1) : d773 p ≤ (4 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d773, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8520 p hg
    simpa only [d773, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d773, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d773, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8567 (p : Pattern) (guard : d985 p = 1) : d774 p ≤ (4 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d774, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8520 p hg
    simpa only [d774, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d774, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8566 p hg
    simpa only [d774, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8568 (p : Pattern) (guard : d985 p = 1) : d774 p ≤ (4 : Int) + d72 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8565 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8567 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8569 (p : Pattern) (guard : d985 p = 1) : d775 p ≤ (4 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d775, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8523 p hg
    simpa only [d775, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d775, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8568 p hg
    simpa only [d775, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8570 (p : Pattern) (guard : d985 p = 1) : d776 p ≤ (4 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d776, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8524 p hg
    simpa only [d776, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d776, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8569 p hg
    simpa only [d776, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8571 (p : Pattern) (guard : d985 p = 1) : d773 p ≤ (4 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8564 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8566 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8572 (p : Pattern) (guard : d985 p = 1) : d777 p ≤ (4 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d777, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8523 p hg
    simpa only [d777, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d777, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8571 p hg
    simpa only [d777, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8573 (p : Pattern) (guard : d985 p = 1) : d778 p ≤ (4 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d778, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8524 p hg
    simpa only [d778, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d778, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8572 p hg
    simpa only [d778, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8574 (p : Pattern) (guard : d985 p = 1) : d779 p ≤ (4 : Int) + d78 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d779, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8570 p hg
    simpa only [d779, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d779, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8573 p hg
    simpa only [d779, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8575 (p : Pattern) (guard : d985 p = 1) : d780 p ≤ (4 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d780, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8542 p hg
    simpa only [d780, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d780, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8571 p hg
    simpa only [d780, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8576 (p : Pattern) (guard : d985 p = 1) : d781 p ≤ (4 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d781, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8543 p hg
    simpa only [d781, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d781, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8575 p hg
    simpa only [d781, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8577 (p : Pattern) (guard : d985 p = 1) : d782 p ≤ (4 : Int) + d81 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d782, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8552 p hg
    simpa only [d782, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d782, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8571 p hg
    simpa only [d782, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8578 (p : Pattern) (guard : d985 p = 1) : d783 p ≤ (4 : Int) + d82 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d783, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8553 p hg
    simpa only [d783, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d783, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8577 p hg
    simpa only [d783, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8579 (p : Pattern) (guard : d985 p = 1) : d784 p ≤ (4 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d784, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8576 p hg
    simpa only [d784, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d784, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8578 p hg
    simpa only [d784, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8580 (p : Pattern) (guard : d985 p = 1) : d785 p ≤ (4 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d785, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8574 p hg
    simpa only [d785, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d785, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8579 p hg
    simpa only [d785, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8581 (p : Pattern) (guard : d985 p = 1) : d786 p ≤ (4 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d786, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8563 p hg
    simpa only [d786, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d786, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8580 p hg
    simpa only [d786, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8582 (p : Pattern) (guard : d985 p = 1) : d787 p ≤ (4 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d787, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8501 p hg
    simpa only [d787, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d787, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8548 p hg
    simpa only [d787, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8583 (p : Pattern) (guard : d985 p = 1) : d788 p ≤ (4 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d788, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8516 p hg
    simpa only [d788, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d788, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8550 p hg
    simpa only [d788, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8584 (p : Pattern) (guard : d985 p = 1) : d789 p ≤ (4 : Int) + d88 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d789, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8582 p hg
    simpa only [d789, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d789, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8583 p hg
    simpa only [d789, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8585 (p : Pattern) (guard : d985 p = 1) : d790 p ≤ (4 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d790, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8582 p hg
    simpa only [d790, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d790, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8584 p hg
    simpa only [d790, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8586 (p : Pattern) (guard : d985 p = 1) : d788 p ≤ (4 : Int) + d90 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d788, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8529 p hg
    simpa only [d788, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d788, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8554 p hg
    simpa only [d788, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8587 (p : Pattern) (guard : d985 p = 1) : d789 p ≤ (4 : Int) + d91 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d789, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8582 p hg
    simpa only [d789, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d789, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8586 p hg
    simpa only [d789, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8588 (p : Pattern) (guard : d985 p = 1) : d788 p ≤ (4 : Int) + d92 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d788, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8534 p hg
    simpa only [d788, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d788, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8557 p hg
    simpa only [d788, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8589 (p : Pattern) (guard : d985 p = 1) : d788 p ≤ (4 : Int) + d93 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8588 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8583 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8590 (p : Pattern) (guard : d985 p = 1) : d791 p ≤ (4 : Int) + d94 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d791, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8587 p hg
    simpa only [d791, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d791, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8589 p hg
    simpa only [d791, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8591 (p : Pattern) (guard : d985 p = 1) : d792 p ≤ (4 : Int) + d95 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d792, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8585 p hg
    simpa only [d792, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d792, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8590 p hg
    simpa only [d792, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8592 (p : Pattern) (guard : d985 p = 1) : d793 p ≤ (4 : Int) + d96 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d793, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8541 p hg
    simpa only [d793, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d793, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8591 p hg
    simpa only [d793, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8593 (p : Pattern) (guard : d985 p = 1) : d794 p ≤ (4 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d794, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8510 p hg
    simpa only [d794, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d794, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d794, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8594 (p : Pattern) (guard : d985 p = 1) : d795 p ≤ (4 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d795, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8510 p hg
    simpa only [d795, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d795, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8593 p hg
    simpa only [d795, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8595 (p : Pattern) (guard : d985 p = 1) : d796 p ≤ (4 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d796, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8594 p hg
    simpa only [d796, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d796, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8567 p hg
    simpa only [d796, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8596 (p : Pattern) (guard : d985 p = 1) : d797 p ≤ (4 : Int) + d100 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d797, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8594 p hg
    simpa only [d797, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d797, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8595 p hg
    simpa only [d797, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8597 (p : Pattern) (guard : d985 p = 1) : d798 p ≤ (4 : Int) + d101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d798, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8595 p hg
    simpa only [d798, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d798, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8568 p hg
    simpa only [d798, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8598 (p : Pattern) (guard : d985 p = 1) : d799 p ≤ (4 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d799, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8596 p hg
    simpa only [d799, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d799, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8597 p hg
    simpa only [d799, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8599 (p : Pattern) (guard : d985 p = 1) : d800 p ≤ (4 : Int) + d103 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d800, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8592 p hg
    simpa only [d800, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d800, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8598 p hg
    simpa only [d800, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8600 (p : Pattern) (guard : d985 p = 1) : d801 p ≤ (4 : Int) + d104 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d801, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8584 p hg
    simpa only [d801, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d801, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8571 p hg
    simpa only [d801, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8601 (p : Pattern) (guard : d985 p = 1) : d802 p ≤ (4 : Int) + d105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d802, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8585 p hg
    simpa only [d802, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d802, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8600 p hg
    simpa only [d802, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8602 (p : Pattern) (guard : d985 p = 1) : d803 p ≤ (4 : Int) + d106 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d803, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8573 p hg
    simpa only [d803, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d803, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8601 p hg
    simpa only [d803, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8603 (p : Pattern) (guard : d985 p = 1) : d804 p ≤ (4 : Int) + d107 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d804, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8595 p hg
    simpa only [d804, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d804, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d804, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8604 (p : Pattern) (guard : d985 p = 1) : d805 p ≤ (4 : Int) + d108 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d805, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8596 p hg
    simpa only [d805, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d805, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8603 p hg
    simpa only [d805, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8605 (p : Pattern) (guard : d985 p = 1) : d806 p ≤ (4 : Int) + d109 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d806, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8593 p hg
    simpa only [d806, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d806, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8566 p hg
    simpa only [d806, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8606 (p : Pattern) (guard : d985 p = 1) : d807 p ≤ (4 : Int) + d110 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d807, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8593 p hg
    simpa only [d807, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d807, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8605 p hg
    simpa only [d807, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8607 (p : Pattern) (guard : d985 p = 1) : d808 p ≤ (4 : Int) + d111 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d808, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8605 p hg
    simpa only [d808, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d808, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d808, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8608 (p : Pattern) (guard : d985 p = 1) : d809 p ≤ (4 : Int) + d112 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d809, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8606 p hg
    simpa only [d809, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d809, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8607 p hg
    simpa only [d809, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8609 (p : Pattern) (guard : d985 p = 1) : d810 p ≤ (4 : Int) + d113 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d810, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8604 p hg
    simpa only [d810, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d810, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8608 p hg
    simpa only [d810, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8610 (p : Pattern) (guard : d985 p = 1) : d811 p ≤ (4 : Int) + d114 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d811, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8602 p hg
    simpa only [d811, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d811, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8609 p hg
    simpa only [d811, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8611 (p : Pattern) (guard : d985 p = 1) : d812 p ≤ (4 : Int) + d115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d812, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8599 p hg
    simpa only [d812, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d812, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8610 p hg
    simpa only [d812, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8612 (p : Pattern) (guard : d985 p = 1) : d813 p ≤ (4 : Int) + d116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d813, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8581 p hg
    simpa only [d813, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d813, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8611 p hg
    simpa only [d813, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8613 (p : Pattern) (guard : d985 p = 1) : d814 p ≤ (4 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d814, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8573 p hg
    simpa only [d814, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d814, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8579 p hg
    simpa only [d814, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8614 (p : Pattern) (guard : d985 p = 1) : d815 p ≤ (4 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d815, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8563 p hg
    simpa only [d815, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d815, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8613 p hg
    simpa only [d815, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8615 (p : Pattern) (guard : d985 p = 1) : d751 p ≤ (4 : Int) + d119 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8529 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8516 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8616 (p : Pattern) (guard : d985 p = 1) : d788 p ≤ (4 : Int) + d120 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d788, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8615 p hg
    simpa only [d788, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d788, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8554 p hg
    simpa only [d788, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8617 (p : Pattern) (guard : d985 p = 1) : d789 p ≤ (4 : Int) + d121 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d789, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8582 p hg
    simpa only [d789, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d789, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8616 p hg
    simpa only [d789, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8618 (p : Pattern) (guard : d985 p = 1) : d791 p ≤ (4 : Int) + d122 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d791, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8617 p hg
    simpa only [d791, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d791, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8589 p hg
    simpa only [d791, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8619 (p : Pattern) (guard : d985 p = 1) : d792 p ≤ (4 : Int) + d123 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d792, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8585 p hg
    simpa only [d792, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d792, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8618 p hg
    simpa only [d792, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8620 (p : Pattern) (guard : d985 p = 1) : d793 p ≤ (4 : Int) + d124 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d793, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8541 p hg
    simpa only [d793, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d793, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8619 p hg
    simpa only [d793, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8621 (p : Pattern) (guard : d985 p = 1) : d816 p ≤ (4 : Int) + d125 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d816, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8605 p hg
    simpa only [d816, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d816, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8571 p hg
    simpa only [d816, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8622 (p : Pattern) (guard : d985 p = 1) : d817 p ≤ (4 : Int) + d126 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d817, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8606 p hg
    simpa only [d817, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d817, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8621 p hg
    simpa only [d817, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8623 (p : Pattern) (guard : d985 p = 1) : d818 p ≤ (4 : Int) + d127 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d818, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8598 p hg
    simpa only [d818, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d818, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8622 p hg
    simpa only [d818, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8624 (p : Pattern) (guard : d985 p = 1) : d819 p ≤ (4 : Int) + d128 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d819, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8620 p hg
    simpa only [d819, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d819, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8623 p hg
    simpa only [d819, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8625 (p : Pattern) (guard : d985 p = 1) : d820 p ≤ (4 : Int) + d129 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d820, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8573 p hg
    simpa only [d820, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d820, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8578 p hg
    simpa only [d820, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8626 (p : Pattern) (guard : d985 p = 1) : d821 p ≤ (4 : Int) + d130 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d821, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8608 p hg
    simpa only [d821, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d821, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d821, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8627 (p : Pattern) (guard : d985 p = 1) : d822 p ≤ (4 : Int) + d131 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d822, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8625 p hg
    simpa only [d822, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d822, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8626 p hg
    simpa only [d822, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8628 (p : Pattern) (guard : d985 p = 1) : d823 p ≤ (4 : Int) + d132 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d823, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8624 p hg
    simpa only [d823, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d823, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8627 p hg
    simpa only [d823, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8629 (p : Pattern) (guard : d985 p = 1) : d824 p ≤ (4 : Int) + d133 p := by
  cases selected : p 86 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d824, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8614 p hg
    simpa only [d824, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d824, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8628 p hg
    simpa only [d824, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8630 (p : Pattern) (guard : d985 p = 1) : d825 p ≤ (4 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d825, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8612 p hg
    simpa only [d825, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d825, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8629 p hg
    simpa only [d825, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8631 (p : Pattern) (guard : d1293 p = 1) : d3 p ≤ (0 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4485 p hg
    simpa only [d1293, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3404 p hg
    simpa only [d1293, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8632 (p : Pattern) (guard : d1293 p = 1) : d743 p ≤ (0 : Int) + d5 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8631 p hg
    simpa only [d743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4486 p hg
    simpa only [d743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8633 (p : Pattern) (guard : d1293 p = 1) : d744 p ≤ (0 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d744, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8631 p hg
    simpa only [d744, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d744, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d744, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8634 (p : Pattern) (guard : d1293 p = 1) : d745 p ≤ (0 : Int) + d697 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d745, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8632 p hg
    simpa only [d745, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d745, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8633 p hg
    simpa only [d745, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8635 (p : Pattern) (guard : d1293 p = 1) : d9 p ≤ (0 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4491 p hg
    simpa only [d1293, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3410 p hg
    simpa only [d1293, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8636 (p : Pattern) (guard : d1293 p = 1) : d746 p ≤ (0 : Int) + d11 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8635 p hg
    simpa only [d746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4492 p hg
    simpa only [d746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8637 (p : Pattern) (guard : d1293 p = 1) : d747 p ≤ (0 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d747, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8635 p hg
    simpa only [d747, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d747, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d747, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8638 (p : Pattern) (guard : d1293 p = 1) : d748 p ≤ (0 : Int) + d698 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d748, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8636 p hg
    simpa only [d748, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d748, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8637 p hg
    simpa only [d748, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8639 (p : Pattern) (guard : d1293 p = 1) : d749 p ≤ (0 : Int) + d699 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d749, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8634 p hg
    simpa only [d749, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d749, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8638 p hg
    simpa only [d749, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8640 (p : Pattern) (guard : d1293 p = 1) : d750 p ≤ (0 : Int) + d700 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d750, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8634 p hg
    simpa only [d750, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d750, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8639 p hg
    simpa only [d750, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8641 (p : Pattern) (guard : d1293 p = 1) : d751 p ≤ (0 : Int) + d697 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d751, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8632 p hg
    simpa only [d751, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d751, d697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4488 p hg
    simpa only [d751, d697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8642 (p : Pattern) (guard : d1293 p = 1) : d752 p ≤ (0 : Int) + d698 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d752, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8636 p hg
    simpa only [d752, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d752, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4494 p hg
    simpa only [d752, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8643 (p : Pattern) (guard : d1293 p = 1) : d753 p ≤ (0 : Int) + d699 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d753, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8641 p hg
    simpa only [d753, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d753, d699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8642 p hg
    simpa only [d753, d699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8644 (p : Pattern) (guard : d1293 p = 1) : d754 p ≤ (0 : Int) + d700 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d754, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8641 p hg
    simpa only [d754, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d754, d700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8643 p hg
    simpa only [d754, d700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8645 (p : Pattern) (guard : d1293 p = 1) : d755 p ≤ (0 : Int) + d700 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8640 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8644 p hg
    simpa only [d755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8646 (p : Pattern) (guard : d1293 p = 1) : d756 p ≤ (0 : Int) + d700 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8640 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8645 p hg
    simpa only [d756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8647 (p : Pattern) (guard : d1293 p = 1) : d757 p ≤ (0 : Int) + d700 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8645 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8644 p hg
    simpa only [d757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8648 (p : Pattern) (guard : d1293 p = 1) : d758 p ≤ (0 : Int) + d700 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8646 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8647 p hg
    simpa only [d758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8649 (p : Pattern) (guard : d1293 p = 1) : d759 p ≤ (0 : Int) + d699 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8639 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8643 p hg
    simpa only [d759, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8650 (p : Pattern) (guard : d1293 p = 1) : d760 p ≤ (0 : Int) + d699 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8639 p hg
    simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8649 p hg
    simpa only [d760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8651 (p : Pattern) (guard : d1293 p = 1) : d761 p ≤ (0 : Int) + d699 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8649 p hg
    simpa only [d761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8643 p hg
    simpa only [d761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8652 (p : Pattern) (guard : d1293 p = 1) : d762 p ≤ (0 : Int) + d699 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8650 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8651 p hg
    simpa only [d762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8653 (p : Pattern) (guard : d1293 p = 1) : d763 p ≤ (0 : Int) + d701 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d763, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8634 p hg
    simpa only [d763, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d763, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d763, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8654 (p : Pattern) (guard : d1293 p = 1) : d764 p ≤ (0 : Int) + d702 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d764, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8639 p hg
    simpa only [d764, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d764, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8653 p hg
    simpa only [d764, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8655 (p : Pattern) (guard : d1293 p = 1) : d765 p ≤ (0 : Int) + d701 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d765, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8641 p hg
    simpa only [d765, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d765, d701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d765, d701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8656 (p : Pattern) (guard : d1293 p = 1) : d766 p ≤ (0 : Int) + d702 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d766, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8643 p hg
    simpa only [d766, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d766, d702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8655 p hg
    simpa only [d766, d702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8657 (p : Pattern) (guard : d1293 p = 1) : d767 p ≤ (0 : Int) + d702 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8654 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8656 p hg
    simpa only [d767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8658 (p : Pattern) (guard : d1293 p = 1) : d768 p ≤ (0 : Int) + d702 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8654 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8657 p hg
    simpa only [d768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8659 (p : Pattern) (guard : d1293 p = 1) : d769 p ≤ (0 : Int) + d702 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8657 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8656 p hg
    simpa only [d769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8660 (p : Pattern) (guard : d1293 p = 1) : d770 p ≤ (0 : Int) + d702 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8658 p hg
    simpa only [d770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8659 p hg
    simpa only [d770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8661 (p : Pattern) (guard : d1293 p = 1) : d771 p ≤ (0 : Int) + d703 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d771, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8652 p hg
    simpa only [d771, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d771, d703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8660 p hg
    simpa only [d771, d703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8662 (p : Pattern) (guard : d1293 p = 1) : d772 p ≤ (0 : Int) + d704 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d772, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8648 p hg
    simpa only [d772, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d772, d704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8661 p hg
    simpa only [d772, d704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8663 (p : Pattern) (guard : d1293 p = 1) : d773 p ≤ (0 : Int) + d705 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d773, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8642 p hg
    simpa only [d773, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d773, d705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d773, d705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8664 (p : Pattern) (guard : d1293 p = 1) : d774 p ≤ (0 : Int) + d706 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d774, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8642 p hg
    simpa only [d774, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d774, d706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8663 p hg
    simpa only [d774, d706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8665 (p : Pattern) (guard : d1293 p = 1) : d775 p ≤ (0 : Int) + d707 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d775, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8645 p hg
    simpa only [d775, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d775, d707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8664 p hg
    simpa only [d775, d707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8666 (p : Pattern) (guard : d1293 p = 1) : d776 p ≤ (0 : Int) + d708 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d776, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8646 p hg
    simpa only [d776, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d776, d708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8665 p hg
    simpa only [d776, d708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8667 (p : Pattern) (guard : d1293 p = 1) : d777 p ≤ (0 : Int) + d709 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d777, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8645 p hg
    simpa only [d777, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d777, d709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8663 p hg
    simpa only [d777, d709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8668 (p : Pattern) (guard : d1293 p = 1) : d778 p ≤ (0 : Int) + d710 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d778, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8646 p hg
    simpa only [d778, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d778, d710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8667 p hg
    simpa only [d778, d710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8669 (p : Pattern) (guard : d1293 p = 1) : d779 p ≤ (0 : Int) + d711 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d779, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8666 p hg
    simpa only [d779, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d779, d711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8668 p hg
    simpa only [d779, d711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8670 (p : Pattern) (guard : d1293 p = 1) : d780 p ≤ (0 : Int) + d712 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d780, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8649 p hg
    simpa only [d780, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d780, d712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8663 p hg
    simpa only [d780, d712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8671 (p : Pattern) (guard : d1293 p = 1) : d781 p ≤ (0 : Int) + d713 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d781, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8650 p hg
    simpa only [d781, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d781, d713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8670 p hg
    simpa only [d781, d713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8672 (p : Pattern) (guard : d1293 p = 1) : d782 p ≤ (0 : Int) + d714 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d782, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8657 p hg
    simpa only [d782, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d782, d714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8663 p hg
    simpa only [d782, d714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8673 (p : Pattern) (guard : d1293 p = 1) : d783 p ≤ (0 : Int) + d715 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d783, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8658 p hg
    simpa only [d783, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d783, d715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8672 p hg
    simpa only [d783, d715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8674 (p : Pattern) (guard : d1293 p = 1) : d784 p ≤ (0 : Int) + d716 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d784, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8671 p hg
    simpa only [d784, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d784, d716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8673 p hg
    simpa only [d784, d716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8675 (p : Pattern) (guard : d1293 p = 1) : d785 p ≤ (0 : Int) + d717 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d785, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8669 p hg
    simpa only [d785, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d785, d717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8674 p hg
    simpa only [d785, d717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8676 (p : Pattern) (guard : d1293 p = 1) : d786 p ≤ (0 : Int) + d718 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d786, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8662 p hg
    simpa only [d786, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d786, d718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8675 p hg
    simpa only [d786, d718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8677 (p : Pattern) (guard : d1293 p = 1) : d787 p ≤ (0 : Int) + d719 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d787, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8634 p hg
    simpa only [d787, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d787, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8653 p hg
    simpa only [d787, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8678 (p : Pattern) (guard : d1293 p = 1) : d788 p ≤ (0 : Int) + d719 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d788, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8641 p hg
    simpa only [d788, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d788, d719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8655 p hg
    simpa only [d788, d719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8679 (p : Pattern) (guard : d1293 p = 1) : d789 p ≤ (0 : Int) + d719 p := by
  cases selected : p 134 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8677 p hg
    simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8678 p hg
    simpa only [d789, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
