/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons059
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8400 (p : Pattern) (guard : d985 p = 1) : d754 p ≤ (0 : Int) + d43 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8399 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8383 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8401 (p : Pattern) (guard : d985 p = 1) : d757 p ≤ (0 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d757, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8393 p hg
    simpa only [d757, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d757, d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8400 p hg
    simpa only [d757, d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8402 (p : Pattern) (guard : d985 p = 1) : d758 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d758, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8385 p hg
    simpa only [d758, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d758, d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8401 p hg
    simpa only [d758, d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8403 (p : Pattern) (guard : d985 p = 1) : d759 p ≤ (0 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d759, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8376 p hg
    simpa only [d759, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d759, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8382 p hg
    simpa only [d759, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8404 (p : Pattern) (guard : d985 p = 1) : d760 p ≤ (0 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d760, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8376 p hg
    simpa only [d760, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d760, d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8403 p hg
    simpa only [d760, d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8405 (p : Pattern) (guard : d985 p = 1) : d759 p ≤ (0 : Int) + d48 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d759, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8376 p hg
    simpa only [d759, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d759, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8391 p hg
    simpa only [d759, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8406 (p : Pattern) (guard : d985 p = 1) : d753 p ≤ (0 : Int) + d49 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8398 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8382 p hg
    simpa only [d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8407 (p : Pattern) (guard : d985 p = 1) : d761 p ≤ (0 : Int) + d50 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d761, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8405 p hg
    simpa only [d761, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d761, d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8406 p hg
    simpa only [d761, d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8408 (p : Pattern) (guard : d985 p = 1) : d762 p ≤ (0 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d762, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8404 p hg
    simpa only [d762, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d762, d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8407 p hg
    simpa only [d762, d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8409 (p : Pattern) (guard : d985 p = 1) : d763 p ≤ (0 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d763, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8370 p hg
    simpa only [d763, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d763, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d763, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8410 (p : Pattern) (guard : d985 p = 1) : d764 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d764, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8376 p hg
    simpa only [d764, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d764, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8409 p hg
    simpa only [d764, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8411 (p : Pattern) (guard : d985 p = 1) : d765 p ≤ (0 : Int) + d54 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d765, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8379 p hg
    simpa only [d765, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d765, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d765, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8412 (p : Pattern) (guard : d985 p = 1) : d766 p ≤ (0 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d766, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8382 p hg
    simpa only [d766, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d766, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8411 p hg
    simpa only [d766, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8413 (p : Pattern) (guard : d985 p = 1) : d767 p ≤ (0 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d767, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8410 p hg
    simpa only [d767, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d767, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8412 p hg
    simpa only [d767, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8414 (p : Pattern) (guard : d985 p = 1) : d768 p ≤ (0 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d768, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8410 p hg
    simpa only [d768, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d768, d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8413 p hg
    simpa only [d768, d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8415 (p : Pattern) (guard : d985 p = 1) : d765 p ≤ (0 : Int) + d58 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d765, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8390 p hg
    simpa only [d765, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d765, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d765, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8416 (p : Pattern) (guard : d985 p = 1) : d766 p ≤ (0 : Int) + d59 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d766, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8391 p hg
    simpa only [d766, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d766, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8415 p hg
    simpa only [d766, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8417 (p : Pattern) (guard : d985 p = 1) : d767 p ≤ (0 : Int) + d60 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d767, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8410 p hg
    simpa only [d767, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d767, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8416 p hg
    simpa only [d767, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8418 (p : Pattern) (guard : d985 p = 1) : d765 p ≤ (0 : Int) + d61 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d765, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8395 p hg
    simpa only [d765, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d765, d61, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d765, d61, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8419 (p : Pattern) (guard : d985 p = 1) : d766 p ≤ (0 : Int) + d62 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d766, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8398 p hg
    simpa only [d766, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d766, d62, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8418 p hg
    simpa only [d766, d62, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8420 (p : Pattern) (guard : d985 p = 1) : d766 p ≤ (0 : Int) + d63 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8419 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8412 p hg
    simpa only [d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8421 (p : Pattern) (guard : d985 p = 1) : d769 p ≤ (0 : Int) + d64 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d769, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8417 p hg
    simpa only [d769, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d769, d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8420 p hg
    simpa only [d769, d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8422 (p : Pattern) (guard : d985 p = 1) : d770 p ≤ (0 : Int) + d65 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8414 p hg
    simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8421 p hg
    simpa only [d770, d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8423 (p : Pattern) (guard : d985 p = 1) : d771 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d771, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8408 p hg
    simpa only [d771, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d771, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8422 p hg
    simpa only [d771, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8424 (p : Pattern) (guard : d985 p = 1) : d772 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d772, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8402 p hg
    simpa only [d772, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d772, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8423 p hg
    simpa only [d772, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8425 (p : Pattern) (guard : d985 p = 1) : d773 p ≤ (0 : Int) + d68 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d773, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8397 p hg
    simpa only [d773, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d773, d68, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d773, d68, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8426 (p : Pattern) (guard : d985 p = 1) : d774 p ≤ (0 : Int) + d69 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d774, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8397 p hg
    simpa only [d774, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d774, d69, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8425 p hg
    simpa only [d774, d69, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8427 (p : Pattern) (guard : d985 p = 1) : d773 p ≤ (0 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d773, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8381 p hg
    simpa only [d773, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d773, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d773, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8428 (p : Pattern) (guard : d985 p = 1) : d774 p ≤ (0 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d774, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8381 p hg
    simpa only [d774, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d774, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8427 p hg
    simpa only [d774, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8429 (p : Pattern) (guard : d985 p = 1) : d774 p ≤ (0 : Int) + d72 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8426 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8428 p hg
    simpa only [d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8430 (p : Pattern) (guard : d985 p = 1) : d775 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d775, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8384 p hg
    simpa only [d775, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d775, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8429 p hg
    simpa only [d775, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8431 (p : Pattern) (guard : d985 p = 1) : d776 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d776, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8385 p hg
    simpa only [d776, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d776, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8430 p hg
    simpa only [d776, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8432 (p : Pattern) (guard : d985 p = 1) : d773 p ≤ (0 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8425 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8427 p hg
    simpa only [d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8433 (p : Pattern) (guard : d985 p = 1) : d777 p ≤ (0 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d777, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8384 p hg
    simpa only [d777, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d777, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8432 p hg
    simpa only [d777, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8434 (p : Pattern) (guard : d985 p = 1) : d778 p ≤ (0 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d778, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8385 p hg
    simpa only [d778, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d778, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8433 p hg
    simpa only [d778, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8435 (p : Pattern) (guard : d985 p = 1) : d779 p ≤ (0 : Int) + d78 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d779, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8431 p hg
    simpa only [d779, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d779, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8434 p hg
    simpa only [d779, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8436 (p : Pattern) (guard : d985 p = 1) : d780 p ≤ (0 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d780, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8403 p hg
    simpa only [d780, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d780, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8432 p hg
    simpa only [d780, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8437 (p : Pattern) (guard : d985 p = 1) : d781 p ≤ (0 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d781, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8404 p hg
    simpa only [d781, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d781, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8436 p hg
    simpa only [d781, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8438 (p : Pattern) (guard : d985 p = 1) : d782 p ≤ (0 : Int) + d81 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d782, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8413 p hg
    simpa only [d782, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d782, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8432 p hg
    simpa only [d782, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8439 (p : Pattern) (guard : d985 p = 1) : d783 p ≤ (0 : Int) + d82 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d783, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8414 p hg
    simpa only [d783, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d783, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8438 p hg
    simpa only [d783, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8440 (p : Pattern) (guard : d985 p = 1) : d784 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d784, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8437 p hg
    simpa only [d784, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d784, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8439 p hg
    simpa only [d784, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8441 (p : Pattern) (guard : d985 p = 1) : d785 p ≤ (0 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d785, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8435 p hg
    simpa only [d785, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d785, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8440 p hg
    simpa only [d785, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8442 (p : Pattern) (guard : d985 p = 1) : d786 p ≤ (0 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d786, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8424 p hg
    simpa only [d786, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d786, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8441 p hg
    simpa only [d786, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8443 (p : Pattern) (guard : d985 p = 1) : d787 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d787, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8370 p hg
    simpa only [d787, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d787, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8409 p hg
    simpa only [d787, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8444 (p : Pattern) (guard : d985 p = 1) : d788 p ≤ (0 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d788, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8379 p hg
    simpa only [d788, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d788, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8411 p hg
    simpa only [d788, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8445 (p : Pattern) (guard : d985 p = 1) : d789 p ≤ (0 : Int) + d88 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d789, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8443 p hg
    simpa only [d789, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d789, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8444 p hg
    simpa only [d789, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8446 (p : Pattern) (guard : d985 p = 1) : d790 p ≤ (0 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d790, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8443 p hg
    simpa only [d790, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d790, d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8445 p hg
    simpa only [d790, d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8447 (p : Pattern) (guard : d985 p = 1) : d788 p ≤ (0 : Int) + d90 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d788, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8390 p hg
    simpa only [d788, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d788, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8415 p hg
    simpa only [d788, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8448 (p : Pattern) (guard : d985 p = 1) : d789 p ≤ (0 : Int) + d91 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d789, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8443 p hg
    simpa only [d789, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d789, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8447 p hg
    simpa only [d789, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8449 (p : Pattern) (guard : d985 p = 1) : d788 p ≤ (0 : Int) + d92 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d788, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8395 p hg
    simpa only [d788, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d788, d92, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8418 p hg
    simpa only [d788, d92, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8450 (p : Pattern) (guard : d985 p = 1) : d788 p ≤ (0 : Int) + d93 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8449 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8444 p hg
    simpa only [d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8451 (p : Pattern) (guard : d985 p = 1) : d791 p ≤ (0 : Int) + d94 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d791, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8448 p hg
    simpa only [d791, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d791, d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8450 p hg
    simpa only [d791, d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8452 (p : Pattern) (guard : d985 p = 1) : d792 p ≤ (0 : Int) + d95 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d792, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8446 p hg
    simpa only [d792, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d792, d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8451 p hg
    simpa only [d792, d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8453 (p : Pattern) (guard : d985 p = 1) : d793 p ≤ (0 : Int) + d96 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d793, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8402 p hg
    simpa only [d793, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d793, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8452 p hg
    simpa only [d793, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8454 (p : Pattern) (guard : d985 p = 1) : d794 p ≤ (0 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d794, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8375 p hg
    simpa only [d794, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d794, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d794, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8455 (p : Pattern) (guard : d985 p = 1) : d795 p ≤ (0 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d795, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8375 p hg
    simpa only [d795, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d795, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8454 p hg
    simpa only [d795, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8456 (p : Pattern) (guard : d985 p = 1) : d796 p ≤ (0 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d796, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8455 p hg
    simpa only [d796, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d796, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8428 p hg
    simpa only [d796, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8457 (p : Pattern) (guard : d985 p = 1) : d797 p ≤ (0 : Int) + d100 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d797, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8455 p hg
    simpa only [d797, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d797, d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8456 p hg
    simpa only [d797, d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8458 (p : Pattern) (guard : d985 p = 1) : d798 p ≤ (0 : Int) + d101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d798, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8456 p hg
    simpa only [d798, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d798, d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8429 p hg
    simpa only [d798, d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8459 (p : Pattern) (guard : d985 p = 1) : d799 p ≤ (0 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d799, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8457 p hg
    simpa only [d799, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d799, d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8458 p hg
    simpa only [d799, d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8460 (p : Pattern) (guard : d985 p = 1) : d800 p ≤ (0 : Int) + d103 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d800, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8453 p hg
    simpa only [d800, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d800, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8459 p hg
    simpa only [d800, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8461 (p : Pattern) (guard : d985 p = 1) : d801 p ≤ (0 : Int) + d104 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d801, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8445 p hg
    simpa only [d801, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d801, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8432 p hg
    simpa only [d801, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8462 (p : Pattern) (guard : d985 p = 1) : d802 p ≤ (0 : Int) + d105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d802, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8446 p hg
    simpa only [d802, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d802, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8461 p hg
    simpa only [d802, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8463 (p : Pattern) (guard : d985 p = 1) : d803 p ≤ (0 : Int) + d106 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d803, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8434 p hg
    simpa only [d803, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d803, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8462 p hg
    simpa only [d803, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8464 (p : Pattern) (guard : d985 p = 1) : d804 p ≤ (0 : Int) + d107 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d804, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8456 p hg
    simpa only [d804, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d804, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d804, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8465 (p : Pattern) (guard : d985 p = 1) : d805 p ≤ (0 : Int) + d108 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d805, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8457 p hg
    simpa only [d805, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d805, d108, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8464 p hg
    simpa only [d805, d108, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8466 (p : Pattern) (guard : d985 p = 1) : d806 p ≤ (0 : Int) + d109 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d806, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8454 p hg
    simpa only [d806, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d806, d109, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8427 p hg
    simpa only [d806, d109, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8467 (p : Pattern) (guard : d985 p = 1) : d807 p ≤ (0 : Int) + d110 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d807, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8454 p hg
    simpa only [d807, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d807, d110, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8466 p hg
    simpa only [d807, d110, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8468 (p : Pattern) (guard : d985 p = 1) : d808 p ≤ (0 : Int) + d111 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d808, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8466 p hg
    simpa only [d808, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d808, d111, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d808, d111, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8469 (p : Pattern) (guard : d985 p = 1) : d809 p ≤ (0 : Int) + d112 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d809, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8467 p hg
    simpa only [d809, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d809, d112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8468 p hg
    simpa only [d809, d112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8470 (p : Pattern) (guard : d985 p = 1) : d810 p ≤ (0 : Int) + d113 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d810, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8465 p hg
    simpa only [d810, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d810, d113, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8469 p hg
    simpa only [d810, d113, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8471 (p : Pattern) (guard : d985 p = 1) : d811 p ≤ (0 : Int) + d114 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d811, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8463 p hg
    simpa only [d811, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d811, d114, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8470 p hg
    simpa only [d811, d114, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8472 (p : Pattern) (guard : d985 p = 1) : d812 p ≤ (0 : Int) + d115 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d812, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8460 p hg
    simpa only [d812, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d812, d115, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8471 p hg
    simpa only [d812, d115, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8473 (p : Pattern) (guard : d985 p = 1) : d813 p ≤ (0 : Int) + d116 p := by
  cases selected : p 86 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d813, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8442 p hg
    simpa only [d813, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d813, d116, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8472 p hg
    simpa only [d813, d116, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8474 (p : Pattern) (guard : d985 p = 1) : d814 p ≤ (0 : Int) + d117 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d814, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8434 p hg
    simpa only [d814, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d814, d117, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8440 p hg
    simpa only [d814, d117, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8475 (p : Pattern) (guard : d985 p = 1) : d815 p ≤ (0 : Int) + d118 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d815, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8424 p hg
    simpa only [d815, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d815, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8474 p hg
    simpa only [d815, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8476 (p : Pattern) (guard : d985 p = 1) : d751 p ≤ (0 : Int) + d119 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8390 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8379 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8477 (p : Pattern) (guard : d985 p = 1) : d788 p ≤ (0 : Int) + d120 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d788, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8476 p hg
    simpa only [d788, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d788, d120, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8415 p hg
    simpa only [d788, d120, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8478 (p : Pattern) (guard : d985 p = 1) : d789 p ≤ (0 : Int) + d121 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d789, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8443 p hg
    simpa only [d789, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d789, d121, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8477 p hg
    simpa only [d789, d121, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8479 (p : Pattern) (guard : d985 p = 1) : d791 p ≤ (0 : Int) + d122 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d791, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8478 p hg
    simpa only [d791, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d791, d122, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8450 p hg
    simpa only [d791, d122, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8480 (p : Pattern) (guard : d985 p = 1) : d792 p ≤ (0 : Int) + d123 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d792, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8446 p hg
    simpa only [d792, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d792, d123, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8479 p hg
    simpa only [d792, d123, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8481 (p : Pattern) (guard : d985 p = 1) : d793 p ≤ (0 : Int) + d124 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d793, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8402 p hg
    simpa only [d793, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d793, d124, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8480 p hg
    simpa only [d793, d124, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8482 (p : Pattern) (guard : d985 p = 1) : d816 p ≤ (0 : Int) + d125 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d816, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8466 p hg
    simpa only [d816, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d816, d125, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8432 p hg
    simpa only [d816, d125, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8483 (p : Pattern) (guard : d985 p = 1) : d817 p ≤ (0 : Int) + d126 p := by
  cases selected : p 132 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d817, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8467 p hg
    simpa only [d817, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d817, d126, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8482 p hg
    simpa only [d817, d126, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8484 (p : Pattern) (guard : d985 p = 1) : d818 p ≤ (0 : Int) + d127 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d818, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8459 p hg
    simpa only [d818, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d818, d127, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8483 p hg
    simpa only [d818, d127, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8485 (p : Pattern) (guard : d985 p = 1) : d819 p ≤ (0 : Int) + d128 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d819, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8481 p hg
    simpa only [d819, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d819, d128, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8484 p hg
    simpa only [d819, d128, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8486 (p : Pattern) (guard : d985 p = 1) : d820 p ≤ (0 : Int) + d129 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d820, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8434 p hg
    simpa only [d820, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d820, d129, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8439 p hg
    simpa only [d820, d129, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8487 (p : Pattern) (guard : d985 p = 1) : d821 p ≤ (0 : Int) + d130 p := by
  cases selected : p 113 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d821, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8469 p hg
    simpa only [d821, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d821, d130, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1218 p hg
    simpa only [d821, d130, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8488 (p : Pattern) (guard : d985 p = 1) : d822 p ≤ (0 : Int) + d131 p := by
  cases selected : p 112 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d822, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8486 p hg
    simpa only [d822, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d822, d131, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8487 p hg
    simpa only [d822, d131, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8489 (p : Pattern) (guard : d985 p = 1) : d823 p ≤ (0 : Int) + d132 p := by
  cases selected : p 106 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d823, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8485 p hg
    simpa only [d823, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d823, d132, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8488 p hg
    simpa only [d823, d132, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8490 (p : Pattern) (guard : d985 p = 1) : d824 p ≤ (0 : Int) + d133 p := by
  cases selected : p 86 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d824, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8475 p hg
    simpa only [d824, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d824, d133, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8489 p hg
    simpa only [d824, d133, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8491 (p : Pattern) (guard : d985 p = 1) : d825 p ≤ (0 : Int) + d134 p := by
  cases selected : p 80 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d825, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8473 p hg
    simpa only [d825, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d825, d134, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8490 p hg
    simpa only [d825, d134, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8492 (p : Pattern) (guard : d1 p = 1) : d0 p ≤ (4 : Int) + d0 p := by
  omega
theorem compare8493 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (4 : Int) + d0 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8494 (p : Pattern) (guard : d985 p = 1) : d3 p ≤ (4 : Int) + d0 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8492 p hg
    simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8493 p hg
    simpa only [d985, d3, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8495 (p : Pattern) (guard : d985 p = 1) : d3 p ≤ (4 : Int) + d3 p := by
  omega
theorem compare8496 (p : Pattern) (guard : d985 p = 1) : d3 p ≤ (4 : Int) + d4 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8494 p hg
    simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8495 p hg
    simpa only [d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8497 (p : Pattern) (guard : d985 p = 1) : d2 p ≤ (4 : Int) + d2 p := by
  omega
theorem compare8498 (p : Pattern) (guard : d985 p = 1) : d17 p ≤ (4 : Int) + d5 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d17, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8494 p hg
    simpa only [d17, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d17, d5, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d17, d5, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8499 (p : Pattern) (guard : d985 p = 1) : d743 p ≤ (4 : Int) + d6 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d743, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8496 p hg
    simpa only [d743, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d743, d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8498 p hg
    simpa only [d743, d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8500 (p : Pattern) (guard : d985 p = 1) : d744 p ≤ (4 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d744, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8496 p hg
    simpa only [d744, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d744, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d744, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8501 (p : Pattern) (guard : d985 p = 1) : d745 p ≤ (4 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d745, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8499 p hg
    simpa only [d745, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d745, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8500 p hg
    simpa only [d745, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8502 (p : Pattern) (guard : d1 p = 1) : d1 p ≤ (4 : Int) + d1 p := by
  omega
theorem compare8503 (p : Pattern) (guard : d0 p = 1) : d2 p ≤ (4 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8504 (p : Pattern) (guard : d985 p = 1) : d9 p ≤ (4 : Int) + d1 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8502 p hg
    simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8503 p hg
    simpa only [d985, d9, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8505 (p : Pattern) (guard : d985 p = 1) : d9 p ≤ (4 : Int) + d9 p := by
  omega
theorem compare8506 (p : Pattern) (guard : d985 p = 1) : d9 p ≤ (4 : Int) + d10 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8504 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8505 p hg
    simpa only [d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8507 (p : Pattern) (guard : d985 p = 1) : d21 p ≤ (4 : Int) + d11 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8504 p hg
    simpa only [d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d21, d11, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8508 (p : Pattern) (guard : d985 p = 1) : d746 p ≤ (4 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d746, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8506 p hg
    simpa only [d746, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d746, d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8507 p hg
    simpa only [d746, d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8509 (p : Pattern) (guard : d985 p = 1) : d747 p ≤ (4 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d747, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8506 p hg
    simpa only [d747, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d747, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d747, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8510 (p : Pattern) (guard : d985 p = 1) : d748 p ≤ (4 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d748, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8508 p hg
    simpa only [d748, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d748, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8509 p hg
    simpa only [d748, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8511 (p : Pattern) (guard : d985 p = 1) : d749 p ≤ (4 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d749, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8501 p hg
    simpa only [d749, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d749, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8510 p hg
    simpa only [d749, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8512 (p : Pattern) (guard : d985 p = 1) : d750 p ≤ (4 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d750, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8501 p hg
    simpa only [d750, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d750, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8511 p hg
    simpa only [d750, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8513 (p : Pattern) (guard : d985 p = 1) : d17 p ≤ (4 : Int) + d17 p := by
  omega
theorem compare8514 (p : Pattern) (guard : d985 p = 1) : d743 p ≤ (4 : Int) + d18 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d743, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8496 p hg
    simpa only [d743, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d743, d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8513 p hg
    simpa only [d743, d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8515 (p : Pattern) (guard : d985 p = 1) : d19 p ≤ (4 : Int) + d19 p := by
  omega
theorem compare8516 (p : Pattern) (guard : d985 p = 1) : d751 p ≤ (4 : Int) + d20 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d751, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8514 p hg
    simpa only [d751, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d751, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8515 p hg
    simpa only [d751, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8517 (p : Pattern) (guard : d985 p = 1) : d21 p ≤ (4 : Int) + d21 p := by
  omega
theorem compare8518 (p : Pattern) (guard : d985 p = 1) : d746 p ≤ (4 : Int) + d22 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d746, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8506 p hg
    simpa only [d746, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d746, d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8517 p hg
    simpa only [d746, d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8519 (p : Pattern) (guard : d985 p = 1) : d23 p ≤ (4 : Int) + d23 p := by
  omega
theorem compare8520 (p : Pattern) (guard : d985 p = 1) : d752 p ≤ (4 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d752, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8518 p hg
    simpa only [d752, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d752, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8519 p hg
    simpa only [d752, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8521 (p : Pattern) (guard : d985 p = 1) : d753 p ≤ (4 : Int) + d25 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d753, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8516 p hg
    simpa only [d753, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d753, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8520 p hg
    simpa only [d753, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8522 (p : Pattern) (guard : d985 p = 1) : d754 p ≤ (4 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d754, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8516 p hg
    simpa only [d754, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d754, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8521 p hg
    simpa only [d754, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8523 (p : Pattern) (guard : d985 p = 1) : d755 p ≤ (4 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d755, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8512 p hg
    simpa only [d755, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d755, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8522 p hg
    simpa only [d755, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8524 (p : Pattern) (guard : d985 p = 1) : d756 p ≤ (4 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d756, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8512 p hg
    simpa only [d756, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d756, d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8523 p hg
    simpa only [d756, d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8525 (p : Pattern) (guard : d985 p = 1) : d3 p ≤ (4 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d3, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8492 p hg
    simpa only [d985, d3, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d3, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8503 p hg
    simpa only [d985, d3, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8526 (p : Pattern) (guard : d985 p = 1) : d17 p ≤ (4 : Int) + d30 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8525 p hg
    simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d17, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8527 (p : Pattern) (guard : d985 p = 1) : d743 p ≤ (4 : Int) + d31 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d743, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8496 p hg
    simpa only [d743, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d743, d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8526 p hg
    simpa only [d743, d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8528 (p : Pattern) (guard : d985 p = 1) : d19 p ≤ (4 : Int) + d32 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8526 p hg
    simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d19, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8529 (p : Pattern) (guard : d985 p = 1) : d751 p ≤ (4 : Int) + d33 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d751, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8527 p hg
    simpa only [d751, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d751, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8528 p hg
    simpa only [d751, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8530 (p : Pattern) (guard : d985 p = 1) : d753 p ≤ (4 : Int) + d34 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d753, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8529 p hg
    simpa only [d753, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d753, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8520 p hg
    simpa only [d753, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8531 (p : Pattern) (guard : d985 p = 1) : d754 p ≤ (4 : Int) + d35 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d754, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8529 p hg
    simpa only [d754, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d754, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8530 p hg
    simpa only [d754, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8532 (p : Pattern) (guard : d985 p = 1) : d755 p ≤ (4 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d755, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8512 p hg
    simpa only [d755, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d755, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8531 p hg
    simpa only [d755, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8533 (p : Pattern) (guard : d985 p = 1) : d19 p ≤ (4 : Int) + d37 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d19, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8498 p hg
    simpa only [d19, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d19, d37, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d19, d37, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8534 (p : Pattern) (guard : d985 p = 1) : d751 p ≤ (4 : Int) + d38 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d751, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8499 p hg
    simpa only [d751, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d751, d38, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8533 p hg
    simpa only [d751, d38, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8535 (p : Pattern) (guard : d985 p = 1) : d23 p ≤ (4 : Int) + d39 p := by
  cases selected : p 159 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8507 p hg
    simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8497 p hg
    simpa only [d23, d39, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8536 (p : Pattern) (guard : d985 p = 1) : d752 p ≤ (4 : Int) + d40 p := by
  cases selected : p 158 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d752, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8508 p hg
    simpa only [d752, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d752, d40, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8535 p hg
    simpa only [d752, d40, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8537 (p : Pattern) (guard : d985 p = 1) : d753 p ≤ (4 : Int) + d41 p := by
  cases selected : p 139 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d753, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8534 p hg
    simpa only [d753, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d753, d41, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8536 p hg
    simpa only [d753, d41, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8538 (p : Pattern) (guard : d985 p = 1) : d754 p ≤ (4 : Int) + d42 p := by
  cases selected : p 138 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d754, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8534 p hg
    simpa only [d754, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d754, d42, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8537 p hg
    simpa only [d754, d42, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8539 (p : Pattern) (guard : d985 p = 1) : d754 p ≤ (4 : Int) + d43 p := by
  cases selected : p 134 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8538 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d985 p = 1 := by simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8522 p hg
    simpa only [d43, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
