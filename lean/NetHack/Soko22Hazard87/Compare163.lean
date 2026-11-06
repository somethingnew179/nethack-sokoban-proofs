import NetHack.Soko22Hazard87.Compare162
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare40750 (p : Pattern) (guard : d324664 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324650 p = 1 := by simpa only [d324664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40749 p hg
    simpa only [d324664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40751 (p : Pattern) (guard : d324652 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324647 p = 1 := by simpa only [d324652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40746 p hg
    simpa only [d324652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40752 (p : Pattern) (guard : d324653 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324652 p = 1 := by simpa only [d324653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40751 p hg
    simpa only [d324653, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324653, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324653, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40753 (p : Pattern) (guard : d324654 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324653 p = 1 := by simpa only [d324654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40752 p hg
    simpa only [d324654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40754 (p : Pattern) (guard : d324665 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324654 p = 1 := by simpa only [d324665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40753 p hg
    simpa only [d324665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40755 (p : Pattern) (guard : d324666 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324664 p = 1 := by simpa only [d324666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40750 p hg
    simpa only [d324666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324665 p = 1 := by simpa only [d324666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40754 p hg
    simpa only [d324666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40756 (p : Pattern) (guard : d324667 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324666 p = 1 := by simpa only [d324667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40755 p hg
    simpa only [d324667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40757 (p : Pattern) (guard : d324668 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324667 p = 1 := by simpa only [d324668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40756 p hg
    simpa only [d324668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40758 (p : Pattern) (guard : d324669 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324668 p = 1 := by simpa only [d324669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40757 p hg
    simpa only [d324669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40759 (p : Pattern) (guard : d324670 p = 1) : d50674 p ≤ (0 : Int) + d324517 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40682 p hg
    simpa only [d324670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324669 p = 1 := by simpa only [d324670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40758 p hg
    simpa only [d324670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40760 (p : Pattern) (guard : d325181 p = 1) : d50675 p ≤ (0 : Int) + d324518 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325181, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d325181, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324670 p = 1 := by simpa only [d325181, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40759 p hg
    simpa only [d325181, d50675, d324518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40761 (p : Pattern) (guard : d325182 p = 1) : d50675 p ≤ (0 : Int) + d324518 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40681 p hg
    simpa only [d325182, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325181 p = 1 := by simpa only [d325182, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40760 p hg
    simpa only [d325182, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40762 (p : Pattern) (guard : d325183 p = 1) : d50675 p ≤ (0 : Int) + d324518 p := by
  cases selected : p 69 with
  | false =>
    have hg : d325182 p = 1 := by simpa only [d325183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40761 p hg
    simpa only [d325183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40681 p hg
    simpa only [d325183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40763 (p : Pattern) (guard : d325184 p = 1) : d50675 p ≤ (0 : Int) + d324518 p := by
  cases selected : p 51 with
  | false =>
    have hg : d325183 p = 1 := by simpa only [d325184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40762 p hg
    simpa only [d325184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40681 p hg
    simpa only [d325184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40764 (p : Pattern) (guard : d325185 p = 1) : d50675 p ≤ (0 : Int) + d324518 p := by
  cases selected : p 50 with
  | false =>
    have hg : d325184 p = 1 := by simpa only [d325185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40763 p hg
    simpa only [d325185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40681 p hg
    simpa only [d325185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40765 (p : Pattern) (guard : d325186 p = 1) : d50676 p ≤ (0 : Int) + d324519 p := by
  cases selected : p 49 with
  | false =>
    have hg : d325180 p = 1 := by simpa only [d325186, d50676, d324519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40680 p hg
    simpa only [d325186, d50676, d324519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325185 p = 1 := by simpa only [d325186, d50676, d324519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40764 p hg
    simpa only [d325186, d50676, d324519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40766 (p : Pattern) (guard : d0 p = 1) : d50739 p ≤ (0 : Int) + d324553 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40767 (p : Pattern) (guard : d0 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40768 (p : Pattern) (guard : d0 p = 1) : d50712 p ≤ (0 : Int) + d324532 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40769 (p : Pattern) (guard : d0 p = 1) : d50724 p ≤ (0 : Int) + d324539 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40770 (p : Pattern) (guard : d0 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40771 (p : Pattern) (guard : d0 p = 1) : d50725 p ≤ (0 : Int) + d49670 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40772 (p : Pattern) (guard : d0 p = 1) : d50560 p ≤ (0 : Int) + d49316 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40773 (p : Pattern) (guard : d0 p = 1) : d47630 p ≤ (0 : Int) + d49316 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40774 (p : Pattern) (guard : d32155 p = 1) : d49316 p ≤ (0 : Int) + d49316 p := by
  omega
theorem compare40775 (p : Pattern) (guard : d324612 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324612, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40773 p hg
    simpa only [d324612, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32155 p = 1 := by simpa only [d324612, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40774 p hg
    simpa only [d324612, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40776 (p : Pattern) (guard : d0 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40777 (p : Pattern) (guard : d324613 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d324612 p = 1 := by simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40775 p hg
    simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40776 p hg
    simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40778 (p : Pattern) (guard : d324614 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d324613 p = 1 := by simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40777 p hg
    simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40776 p hg
    simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40779 (p : Pattern) (guard : d0 p = 1) : d49317 p ≤ (0 : Int) + d49316 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40780 (p : Pattern) (guard : d324615 p = 1) : d50560 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 182 with
  | false =>
    have hg : d324614 p = 1 := by simpa only [d324615, d50560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40778 p hg
    simpa only [d324615, d50560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324615, d50560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40779 p hg
    simpa only [d324615, d50560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40781 (p : Pattern) (guard : d324616 p = 1) : d50560 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40772 p hg
    simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324615 p = 1 := by simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40780 p hg
    simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40782 (p : Pattern) (guard : d324781 p = 1) : d50726 p ≤ (0 : Int) + d324540 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324781, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40771 p hg
    simpa only [d324781, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324616 p = 1 := by simpa only [d324781, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40781 p hg
    simpa only [d324781, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40783 (p : Pattern) (guard : d324617 p = 1) : d50727 p ≤ (0 : Int) + d324541 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324616 p = 1 := by simpa only [d324617, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40604 p hg
    simpa only [d324617, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324617, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40698 p hg
    simpa only [d324617, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40784 (p : Pattern) (guard : d324782 p = 1) : d50728 p ≤ (0 : Int) + d324542 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324781 p = 1 := by simpa only [d324782, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40782 p hg
    simpa only [d324782, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324617 p = 1 := by simpa only [d324782, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40783 p hg
    simpa only [d324782, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40785 (p : Pattern) (guard : d0 p = 1) : d50562 p ≤ (0 : Int) + d49323 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40786 (p : Pattern) (guard : d0 p = 1) : d47634 p ≤ (0 : Int) + d49323 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40787 (p : Pattern) (guard : d32155 p = 1) : d49323 p ≤ (0 : Int) + d49323 p := by
  omega
theorem compare40788 (p : Pattern) (guard : d324612 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324612, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40786 p hg
    simpa only [d324612, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d32155 p = 1 := by simpa only [d324612, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40787 p hg
    simpa only [d324612, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40789 (p : Pattern) (guard : d0 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40790 (p : Pattern) (guard : d324613 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d324612 p = 1 := by simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40788 p hg
    simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d324613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40791 (p : Pattern) (guard : d324614 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d324613 p = 1 := by simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40790 p hg
    simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d324614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40792 (p : Pattern) (guard : d0 p = 1) : d49324 p ≤ (0 : Int) + d49323 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40793 (p : Pattern) (guard : d324615 p = 1) : d50562 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 182 with
  | false =>
    have hg : d324614 p = 1 := by simpa only [d324615, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40791 p hg
    simpa only [d324615, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324615, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40792 p hg
    simpa only [d324615, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40794 (p : Pattern) (guard : d324616 p = 1) : d50562 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40785 p hg
    simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324615 p = 1 := by simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40793 p hg
    simpa only [d324616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40795 (p : Pattern) (guard : d324617 p = 1) : d50573 p ≤ (0 : Int) + d324440 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324616 p = 1 := by simpa only [d324617, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40794 p hg
    simpa only [d324617, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324617, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d324617, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40796 (p : Pattern) (guard : d324618 p = 1) : d50574 p ≤ (0 : Int) + d324441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324617 p = 1 := by simpa only [d324618, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40795 p hg
    simpa only [d324618, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324618, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d324618, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40797 (p : Pattern) (guard : d324783 p = 1) : d50729 p ≤ (0 : Int) + d324543 p := by
  cases selected : p 161 with
  | false =>
    have hg : d324782 p = 1 := by simpa only [d324783, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40784 p hg
    simpa only [d324783, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324618 p = 1 := by simpa only [d324783, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40796 p hg
    simpa only [d324783, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40798 (p : Pattern) (guard : d0 p = 1) : d50732 p ≤ (0 : Int) + d324546 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40799 (p : Pattern) (guard : d324784 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324783 p = 1 := by simpa only [d324784, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40797 p hg
    simpa only [d324784, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324784, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40798 p hg
    simpa only [d324784, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40800 (p : Pattern) (guard : d324785 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40770 p hg
    simpa only [d324785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324784 p = 1 := by simpa only [d324785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40799 p hg
    simpa only [d324785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40801 (p : Pattern) (guard : d1115 p = 1) : d49316 p ≤ (0 : Int) + d49316 p := by
  omega
theorem compare40802 (p : Pattern) (guard : d221076 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221076, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40773 p hg
    simpa only [d221076, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d221076, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40801 p hg
    simpa only [d221076, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40803 (p : Pattern) (guard : d221096 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221076 p = 1 := by simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40802 p hg
    simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40776 p hg
    simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40804 (p : Pattern) (guard : d19 p = 1) : d49316 p ≤ (0 : Int) + d49316 p := by
  omega
theorem compare40805 (p : Pattern) (guard : d221097 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221097, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40773 p hg
    simpa only [d221097, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19 p = 1 := by simpa only [d221097, d50534, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40804 p hg
    simpa only [d221097, d50534, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40806 (p : Pattern) (guard : d221098 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221097 p = 1 := by simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40805 p hg
    simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40776 p hg
    simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40807 (p : Pattern) (guard : d221099 p = 1) : d50534 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 201 with
  | false =>
    have hg : d221096 p = 1 := by simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40803 p hg
    simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221098 p = 1 := by simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40806 p hg
    simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40808 (p : Pattern) (guard : d221100 p = 1) : d50560 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 182 with
  | false =>
    have hg : d221099 p = 1 := by simpa only [d221100, d50560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40807 p hg
    simpa only [d221100, d50560, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221100, d50560, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40779 p hg
    simpa only [d221100, d50560, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40809 (p : Pattern) (guard : d324622 p = 1) : d50560 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 180 with
  | false =>
    have hg : d324615 p = 1 := by simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40780 p hg
    simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221100 p = 1 := by simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40808 p hg
    simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40810 (p : Pattern) (guard : d324787 p = 1) : d50726 p ≤ (0 : Int) + d324540 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324787, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40771 p hg
    simpa only [d324787, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324622 p = 1 := by simpa only [d324787, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40809 p hg
    simpa only [d324787, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40811 (p : Pattern) (guard : d324623 p = 1) : d50727 p ≤ (0 : Int) + d324541 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324622 p = 1 := by simpa only [d324623, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40621 p hg
    simpa only [d324623, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324623, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40698 p hg
    simpa only [d324623, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40812 (p : Pattern) (guard : d324788 p = 1) : d50728 p ≤ (0 : Int) + d324542 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324787 p = 1 := by simpa only [d324788, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40810 p hg
    simpa only [d324788, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324623 p = 1 := by simpa only [d324788, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40811 p hg
    simpa only [d324788, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40813 (p : Pattern) (guard : d1115 p = 1) : d49323 p ≤ (0 : Int) + d49323 p := by
  omega
theorem compare40814 (p : Pattern) (guard : d221076 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221076, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40786 p hg
    simpa only [d221076, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d221076, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40813 p hg
    simpa only [d221076, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40815 (p : Pattern) (guard : d221096 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221076 p = 1 := by simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40814 p hg
    simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d221096, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40816 (p : Pattern) (guard : d19 p = 1) : d49323 p ≤ (0 : Int) + d49323 p := by
  omega
theorem compare40817 (p : Pattern) (guard : d221097 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221097, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40786 p hg
    simpa only [d221097, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d19 p = 1 := by simpa only [d221097, d50561, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40816 p hg
    simpa only [d221097, d50561, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40818 (p : Pattern) (guard : d221098 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221097 p = 1 := by simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40817 p hg
    simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40789 p hg
    simpa only [d221098, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40819 (p : Pattern) (guard : d221099 p = 1) : d50561 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 201 with
  | false =>
    have hg : d221096 p = 1 := by simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40815 p hg
    simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221098 p = 1 := by simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40818 p hg
    simpa only [d221099, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40820 (p : Pattern) (guard : d221100 p = 1) : d50562 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 182 with
  | false =>
    have hg : d221099 p = 1 := by simpa only [d221100, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40819 p hg
    simpa only [d221100, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221100, d50562, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40792 p hg
    simpa only [d221100, d50562, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40821 (p : Pattern) (guard : d324622 p = 1) : d50562 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 180 with
  | false =>
    have hg : d324615 p = 1 := by simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40793 p hg
    simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221100 p = 1 := by simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40820 p hg
    simpa only [d324622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40822 (p : Pattern) (guard : d324623 p = 1) : d50573 p ≤ (0 : Int) + d324440 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324622 p = 1 := by simpa only [d324623, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40821 p hg
    simpa only [d324623, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324623, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d324623, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40823 (p : Pattern) (guard : d324624 p = 1) : d50574 p ≤ (0 : Int) + d324441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324623 p = 1 := by simpa only [d324624, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40822 p hg
    simpa only [d324624, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324624, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d324624, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40824 (p : Pattern) (guard : d324789 p = 1) : d50729 p ≤ (0 : Int) + d324543 p := by
  cases selected : p 161 with
  | false =>
    have hg : d324788 p = 1 := by simpa only [d324789, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40812 p hg
    simpa only [d324789, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324624 p = 1 := by simpa only [d324789, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40823 p hg
    simpa only [d324789, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40825 (p : Pattern) (guard : d324790 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324789 p = 1 := by simpa only [d324790, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40824 p hg
    simpa only [d324790, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324790, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40798 p hg
    simpa only [d324790, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40826 (p : Pattern) (guard : d324791 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324784 p = 1 := by simpa only [d324791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40799 p hg
    simpa only [d324791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324790 p = 1 := by simpa only [d324791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40825 p hg
    simpa only [d324791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40827 (p : Pattern) (guard : d324792 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324785 p = 1 := by simpa only [d324792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40800 p hg
    simpa only [d324792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324791 p = 1 := by simpa only [d324792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40826 p hg
    simpa only [d324792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40828 (p : Pattern) (guard : d324796 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324790 p = 1 := by simpa only [d324796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40825 p hg
    simpa only [d324796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40770 p hg
    simpa only [d324796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40829 (p : Pattern) (guard : d324797 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324791 p = 1 := by simpa only [d324797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40826 p hg
    simpa only [d324797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324796 p = 1 := by simpa only [d324797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40828 p hg
    simpa only [d324797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40830 (p : Pattern) (guard : d324798 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324792 p = 1 := by simpa only [d324798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40827 p hg
    simpa only [d324798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324797 p = 1 := by simpa only [d324798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40829 p hg
    simpa only [d324798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40831 (p : Pattern) (guard : d324799 p = 1) : d50734 p ≤ (0 : Int) + d324548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324799, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40769 p hg
    simpa only [d324799, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324798 p = 1 := by simpa only [d324799, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40830 p hg
    simpa only [d324799, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40832 (p : Pattern) (guard : d324800 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324800, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40768 p hg
    simpa only [d324800, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324799 p = 1 := by simpa only [d324800, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40831 p hg
    simpa only [d324800, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40833 (p : Pattern) (guard : d221101 p = 1) : d50560 p ≤ (0 : Int) + d49316 p := by
  cases selected : p 180 with
  | false =>
    have hg : d221100 p = 1 := by simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40808 p hg
    simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40772 p hg
    simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40834 (p : Pattern) (guard : d221342 p = 1) : d50726 p ≤ (0 : Int) + d324540 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221342, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40771 p hg
    simpa only [d221342, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221101 p = 1 := by simpa only [d221342, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40833 p hg
    simpa only [d221342, d50726, d324540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40835 (p : Pattern) (guard : d221102 p = 1) : d50727 p ≤ (0 : Int) + d324541 p := by
  cases selected : p 163 with
  | false =>
    have hg : d221101 p = 1 := by simpa only [d221102, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40633 p hg
    simpa only [d221102, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221102, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40698 p hg
    simpa only [d221102, d50727, d324541, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40836 (p : Pattern) (guard : d221343 p = 1) : d50728 p ≤ (0 : Int) + d324542 p := by
  cases selected : p 162 with
  | false =>
    have hg : d221342 p = 1 := by simpa only [d221343, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40834 p hg
    simpa only [d221343, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221102 p = 1 := by simpa only [d221343, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40835 p hg
    simpa only [d221343, d50728, d324542, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40837 (p : Pattern) (guard : d221101 p = 1) : d50562 p ≤ (0 : Int) + d49323 p := by
  cases selected : p 180 with
  | false =>
    have hg : d221100 p = 1 := by simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40820 p hg
    simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40785 p hg
    simpa only [d221101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40838 (p : Pattern) (guard : d221102 p = 1) : d50573 p ≤ (0 : Int) + d324440 p := by
  cases selected : p 163 with
  | false =>
    have hg : d221101 p = 1 := by simpa only [d221102, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40837 p hg
    simpa only [d221102, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221102, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d221102, d50573, d324440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40839 (p : Pattern) (guard : d221103 p = 1) : d50574 p ≤ (0 : Int) + d324441 p := by
  cases selected : p 162 with
  | false =>
    have hg : d221102 p = 1 := by simpa only [d221103, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40838 p hg
    simpa only [d221103, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221103, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d221103, d50574, d324441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40840 (p : Pattern) (guard : d221344 p = 1) : d50729 p ≤ (0 : Int) + d324543 p := by
  cases selected : p 161 with
  | false =>
    have hg : d221343 p = 1 := by simpa only [d221344, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40836 p hg
    simpa only [d221344, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221103 p = 1 := by simpa only [d221344, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40839 p hg
    simpa only [d221344, d50729, d324543, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40841 (p : Pattern) (guard : d221345 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 160 with
  | false =>
    have hg : d221344 p = 1 := by simpa only [d221345, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40840 p hg
    simpa only [d221345, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221345, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40798 p hg
    simpa only [d221345, d50733, d324547, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40842 (p : Pattern) (guard : d221346 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 159 with
  | false =>
    have hg : d221345 p = 1 := by simpa only [d221346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40841 p hg
    simpa only [d221346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40770 p hg
    simpa only [d221346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40843 (p : Pattern) (guard : d324802 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324796 p = 1 := by simpa only [d324802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40828 p hg
    simpa only [d324802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221346 p = 1 := by simpa only [d324802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40842 p hg
    simpa only [d324802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40844 (p : Pattern) (guard : d324803 p = 1) : d50733 p ≤ (0 : Int) + d324547 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324797 p = 1 := by simpa only [d324803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40829 p hg
    simpa only [d324803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324802 p = 1 := by simpa only [d324803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40843 p hg
    simpa only [d324803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40845 (p : Pattern) (guard : d324804 p = 1) : d50734 p ≤ (0 : Int) + d324548 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324804, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40769 p hg
    simpa only [d324804, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324803 p = 1 := by simpa only [d324804, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40844 p hg
    simpa only [d324804, d50734, d324548, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40846 (p : Pattern) (guard : d324805 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324805, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40768 p hg
    simpa only [d324805, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324804 p = 1 := by simpa only [d324805, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40845 p hg
    simpa only [d324805, d50735, d324549, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40847 (p : Pattern) (guard : d324806 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324800 p = 1 := by simpa only [d324806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40832 p hg
    simpa only [d324806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324805 p = 1 := by simpa only [d324806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40846 p hg
    simpa only [d324806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40848 (p : Pattern) (guard : d0 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40849 (p : Pattern) (guard : d324811 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324805 p = 1 := by simpa only [d324811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40846 p hg
    simpa only [d324811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d324811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40850 (p : Pattern) (guard : d324812 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324806 p = 1 := by simpa only [d324812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40847 p hg
    simpa only [d324812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324811 p = 1 := by simpa only [d324812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40849 p hg
    simpa only [d324812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40851 (p : Pattern) (guard : d324813 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324812 p = 1 := by simpa only [d324813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40850 p hg
    simpa only [d324813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d324813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40852 (p : Pattern) (guard : d0 p = 1) : d50736 p ≤ (0 : Int) + d324550 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40853 (p : Pattern) (guard : d324814 p = 1) : d50737 p ≤ (0 : Int) + d324551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324813 p = 1 := by simpa only [d324814, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40851 p hg
    simpa only [d324814, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324814, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40852 p hg
    simpa only [d324814, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40854 (p : Pattern) (guard : d324815 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324815, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40590 p hg
    simpa only [d324815, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324814 p = 1 := by simpa only [d324815, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40853 p hg
    simpa only [d324815, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40855 (p : Pattern) (guard : d324820 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324811 p = 1 := by simpa only [d324820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40849 p hg
    simpa only [d324820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d324820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40856 (p : Pattern) (guard : d324821 p = 1) : d50735 p ≤ (0 : Int) + d324549 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324820 p = 1 := by simpa only [d324821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40855 p hg
    simpa only [d324821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40848 p hg
    simpa only [d324821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40857 (p : Pattern) (guard : d324822 p = 1) : d50737 p ≤ (0 : Int) + d324551 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324821 p = 1 := by simpa only [d324822, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40856 p hg
    simpa only [d324822, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324822, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40852 p hg
    simpa only [d324822, d50737, d324551, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40858 (p : Pattern) (guard : d324823 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324823, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40590 p hg
    simpa only [d324823, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324822 p = 1 := by simpa only [d324823, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40857 p hg
    simpa only [d324823, d50738, d324552, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40859 (p : Pattern) (guard : d324824 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324815 p = 1 := by simpa only [d324824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40854 p hg
    simpa only [d324824, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324823 p = 1 := by simpa only [d324824, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40858 p hg
    simpa only [d324824, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40860 (p : Pattern) (guard : d324825 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324824 p = 1 := by simpa only [d324825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40859 p hg
    simpa only [d324825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d324825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40861 (p : Pattern) (guard : d324826 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324825 p = 1 := by simpa only [d324826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40860 p hg
    simpa only [d324826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d324826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40862 (p : Pattern) (guard : d324827 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324826 p = 1 := by simpa only [d324827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40861 p hg
    simpa only [d324827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d324827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40863 (p : Pattern) (guard : d324856 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324823 p = 1 := by simpa only [d324856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40858 p hg
    simpa only [d324856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d324856, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40864 (p : Pattern) (guard : d324857 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324856 p = 1 := by simpa only [d324857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40863 p hg
    simpa only [d324857, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324857, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d324857, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40865 (p : Pattern) (guard : d324858 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324857 p = 1 := by simpa only [d324858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40864 p hg
    simpa only [d324858, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324858, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d324858, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40866 (p : Pattern) (guard : d324859 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324858 p = 1 := by simpa only [d324859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40865 p hg
    simpa only [d324859, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324859, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d324859, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40867 (p : Pattern) (guard : d325187 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324827 p = 1 := by simpa only [d325187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40862 p hg
    simpa only [d325187, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324859 p = 1 := by simpa only [d325187, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40866 p hg
    simpa only [d325187, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40868 (p : Pattern) (guard : d325188 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d325188, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325187 p = 1 := by simpa only [d325188, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40867 p hg
    simpa only [d325188, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40869 (p : Pattern) (guard : d325189 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 89 with
  | false =>
    have hg : d325188 p = 1 := by simpa only [d325189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40868 p hg
    simpa only [d325189, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325189, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d325189, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40870 (p : Pattern) (guard : d325190 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d325190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325189 p = 1 := by simpa only [d325190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40869 p hg
    simpa only [d325190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40871 (p : Pattern) (guard : d325191 p = 1) : d50738 p ≤ (0 : Int) + d324552 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40767 p hg
    simpa only [d325191, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325190 p = 1 := by simpa only [d325191, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40870 p hg
    simpa only [d325191, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40872 (p : Pattern) (guard : d325192 p = 1) : d50739 p ≤ (0 : Int) + d324553 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325192, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d325192, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325191 p = 1 := by simpa only [d325192, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40871 p hg
    simpa only [d325192, d50739, d324553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40873 (p : Pattern) (guard : d325193 p = 1) : d50739 p ≤ (0 : Int) + d324553 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40766 p hg
    simpa only [d325193, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325192 p = 1 := by simpa only [d325193, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40872 p hg
    simpa only [d325193, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40874 (p : Pattern) (guard : d325194 p = 1) : d50739 p ≤ (0 : Int) + d324553 p := by
  cases selected : p 69 with
  | false =>
    have hg : d325193 p = 1 := by simpa only [d325194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40873 p hg
    simpa only [d325194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40766 p hg
    simpa only [d325194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40875 (p : Pattern) (guard : d325195 p = 1) : d50739 p ≤ (0 : Int) + d324553 p := by
  cases selected : p 51 with
  | false =>
    have hg : d325194 p = 1 := by simpa only [d325195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40874 p hg
    simpa only [d325195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40766 p hg
    simpa only [d325195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40876 (p : Pattern) (guard : d325196 p = 1) : d50739 p ≤ (0 : Int) + d324553 p := by
  cases selected : p 50 with
  | false =>
    have hg : d325195 p = 1 := by simpa only [d325196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40875 p hg
    simpa only [d325196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40766 p hg
    simpa only [d325196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40877 (p : Pattern) (guard : d0 p = 1) : d50821 p ≤ (0 : Int) + d324609 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare40878 (p : Pattern) (guard : d325197 p = 1) : d50822 p ≤ (0 : Int) + d324610 p := by
  cases selected : p 49 with
  | false =>
    have hg : d325196 p = 1 := by simpa only [d325197, d50822, d324610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40876 p hg
    simpa only [d325197, d50822, d324610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325197, d50822, d324610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40877 p hg
    simpa only [d325197, d50822, d324610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40879 (p : Pattern) (guard : d325198 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 48 with
  | false =>
    have hg : d325186 p = 1 := by simpa only [d325198, d50823, d324611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40765 p hg
    simpa only [d325198, d50823, d324611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325197 p = 1 := by simpa only [d325198, d50823, d324611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40878 p hg
    simpa only [d325198, d50823, d324611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40880 (p : Pattern) (guard : d325199 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325198 p = 1 := by simpa only [d325199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40879 p hg
    simpa only [d325199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40881 (p : Pattern) (guard : d325200 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325199 p = 1 := by simpa only [d325200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40880 p hg
    simpa only [d325200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40882 (p : Pattern) (guard : d325201 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325200 p = 1 := by simpa only [d325201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40881 p hg
    simpa only [d325201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40883 (p : Pattern) (guard : d325202 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325201 p = 1 := by simpa only [d325202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40882 p hg
    simpa only [d325202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40884 (p : Pattern) (guard : d325203 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325202 p = 1 := by simpa only [d325203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40883 p hg
    simpa only [d325203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40885 (p : Pattern) (guard : d325204 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325204, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325203 p = 1 := by simpa only [d325204, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40884 p hg
    simpa only [d325204, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40886 (p : Pattern) (guard : d325205 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325204 p = 1 := by simpa only [d325205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40885 p hg
    simpa only [d325205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40887 (p : Pattern) (guard : d325206 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325205 p = 1 := by simpa only [d325206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40886 p hg
    simpa only [d325206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40888 (p : Pattern) (guard : d325207 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325206 p = 1 := by simpa only [d325207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40887 p hg
    simpa only [d325207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40889 (p : Pattern) (guard : d325208 p = 1) : d50823 p ≤ (0 : Int) + d324611 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40588 p hg
    simpa only [d325208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325207 p = 1 := by simpa only [d325208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40888 p hg
    simpa only [d325208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40890 (p : Pattern) (guard : d10055 p = 1) : d49396 p ≤ (0 : Int) + d49396 p := by
  omega
theorem compare40891 (p : Pattern) (guard : d38167 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38167, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40596 p hg
    simpa only [d38167, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10055 p = 1 := by simpa only [d38167, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40890 p hg
    simpa only [d38167, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40892 (p : Pattern) (guard : d38168 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d38167 p = 1 := by simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40891 p hg
    simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40599 p hg
    simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40893 (p : Pattern) (guard : d38169 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d38168 p = 1 := by simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40892 p hg
    simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40599 p hg
    simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40894 (p : Pattern) (guard : d38170 p = 1) : d50553 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 182 with
  | false =>
    have hg : d38169 p = 1 := by simpa only [d38170, d50553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40893 p hg
    simpa only [d38170, d50553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38170, d50553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40602 p hg
    simpa only [d38170, d50553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40895 (p : Pattern) (guard : d38177 p = 1) : d50553 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40595 p hg
    simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38170 p = 1 := by simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40894 p hg
    simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40896 (p : Pattern) (guard : d38178 p = 1) : d50570 p ≤ (0 : Int) + d324455 p := by
  cases selected : p 163 with
  | false =>
    have hg : d38177 p = 1 := by simpa only [d38178, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40895 p hg
    simpa only [d38178, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38178, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40605 p hg
    simpa only [d38178, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40897 (p : Pattern) (guard : d38179 p = 1) : d50571 p ≤ (0 : Int) + d324456 p := by
  cases selected : p 162 with
  | false =>
    have hg : d38178 p = 1 := by simpa only [d38179, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40896 p hg
    simpa only [d38179, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38179, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40607 p hg
    simpa only [d38179, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40898 (p : Pattern) (guard : d38180 p = 1) : d50572 p ≤ (0 : Int) + d324457 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38180, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40594 p hg
    simpa only [d38180, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38179 p = 1 := by simpa only [d38180, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40897 p hg
    simpa only [d38180, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40899 (p : Pattern) (guard : d38181 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 160 with
  | false =>
    have hg : d38180 p = 1 := by simpa only [d38181, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40898 p hg
    simpa only [d38181, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38181, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40610 p hg
    simpa only [d38181, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40900 (p : Pattern) (guard : d38302 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40593 p hg
    simpa only [d38302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38181 p = 1 := by simpa only [d38302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40899 p hg
    simpa only [d38302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40901 (p : Pattern) (guard : d2043 p = 1) : d49396 p ≤ (0 : Int) + d49396 p := by
  omega
theorem compare40902 (p : Pattern) (guard : d221468 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221468, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40596 p hg
    simpa only [d221468, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d221468, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40901 p hg
    simpa only [d221468, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40903 (p : Pattern) (guard : d221488 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221468 p = 1 := by simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40902 p hg
    simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40599 p hg
    simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40904 (p : Pattern) (guard : d10406 p = 1) : d49396 p ≤ (0 : Int) + d49396 p := by
  omega
theorem compare40905 (p : Pattern) (guard : d221489 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221489, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40596 p hg
    simpa only [d221489, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10406 p = 1 := by simpa only [d221489, d50510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40904 p hg
    simpa only [d221489, d50510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40906 (p : Pattern) (guard : d221490 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221489 p = 1 := by simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40905 p hg
    simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40599 p hg
    simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40907 (p : Pattern) (guard : d221491 p = 1) : d50510 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 201 with
  | false =>
    have hg : d221488 p = 1 := by simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40903 p hg
    simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221490 p = 1 := by simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40906 p hg
    simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40908 (p : Pattern) (guard : d221492 p = 1) : d50553 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 182 with
  | false =>
    have hg : d221491 p = 1 := by simpa only [d221492, d50553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40907 p hg
    simpa only [d221492, d50553, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221492, d50553, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40602 p hg
    simpa only [d221492, d50553, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40909 (p : Pattern) (guard : d324882 p = 1) : d50553 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 180 with
  | false =>
    have hg : d38170 p = 1 := by simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40894 p hg
    simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221492 p = 1 := by simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40908 p hg
    simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40910 (p : Pattern) (guard : d324883 p = 1) : d50570 p ≤ (0 : Int) + d324455 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324882 p = 1 := by simpa only [d324883, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40909 p hg
    simpa only [d324883, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324883, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40605 p hg
    simpa only [d324883, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40911 (p : Pattern) (guard : d324884 p = 1) : d50571 p ≤ (0 : Int) + d324456 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324883 p = 1 := by simpa only [d324884, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40910 p hg
    simpa only [d324884, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324884, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40607 p hg
    simpa only [d324884, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40912 (p : Pattern) (guard : d324885 p = 1) : d50572 p ≤ (0 : Int) + d324457 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324885, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40594 p hg
    simpa only [d324885, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324884 p = 1 := by simpa only [d324885, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40911 p hg
    simpa only [d324885, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40913 (p : Pattern) (guard : d324886 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324885 p = 1 := by simpa only [d324886, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40912 p hg
    simpa only [d324886, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324886, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40610 p hg
    simpa only [d324886, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40914 (p : Pattern) (guard : d324887 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d38181 p = 1 := by simpa only [d324887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40899 p hg
    simpa only [d324887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324886 p = 1 := by simpa only [d324887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40913 p hg
    simpa only [d324887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40915 (p : Pattern) (guard : d324888 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d38302 p = 1 := by simpa only [d324888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40900 p hg
    simpa only [d324888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324887 p = 1 := by simpa only [d324888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40914 p hg
    simpa only [d324888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40916 (p : Pattern) (guard : d324889 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324886 p = 1 := by simpa only [d324889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40913 p hg
    simpa only [d324889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40593 p hg
    simpa only [d324889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40917 (p : Pattern) (guard : d324890 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324887 p = 1 := by simpa only [d324890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40914 p hg
    simpa only [d324890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324889 p = 1 := by simpa only [d324890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40916 p hg
    simpa only [d324890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40918 (p : Pattern) (guard : d324891 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324888 p = 1 := by simpa only [d324891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40915 p hg
    simpa only [d324891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324890 p = 1 := by simpa only [d324891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40917 p hg
    simpa only [d324891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40919 (p : Pattern) (guard : d324892 p = 1) : d50577 p ≤ (0 : Int) + d324459 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324892, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40592 p hg
    simpa only [d324892, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324891 p = 1 := by simpa only [d324892, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40918 p hg
    simpa only [d324892, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40920 (p : Pattern) (guard : d324893 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324893, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40591 p hg
    simpa only [d324893, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324892 p = 1 := by simpa only [d324893, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40919 p hg
    simpa only [d324893, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40921 (p : Pattern) (guard : d221493 p = 1) : d50553 p ≤ (0 : Int) + d49396 p := by
  cases selected : p 180 with
  | false =>
    have hg : d221492 p = 1 := by simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40908 p hg
    simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40595 p hg
    simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40922 (p : Pattern) (guard : d221494 p = 1) : d50570 p ≤ (0 : Int) + d324455 p := by
  cases selected : p 163 with
  | false =>
    have hg : d221493 p = 1 := by simpa only [d221494, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40921 p hg
    simpa only [d221494, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221494, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40605 p hg
    simpa only [d221494, d50570, d324455, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40923 (p : Pattern) (guard : d221495 p = 1) : d50571 p ≤ (0 : Int) + d324456 p := by
  cases selected : p 162 with
  | false =>
    have hg : d221494 p = 1 := by simpa only [d221495, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40922 p hg
    simpa only [d221495, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221495, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40607 p hg
    simpa only [d221495, d50571, d324456, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40924 (p : Pattern) (guard : d221496 p = 1) : d50572 p ≤ (0 : Int) + d324457 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221496, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40594 p hg
    simpa only [d221496, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221495 p = 1 := by simpa only [d221496, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40923 p hg
    simpa only [d221496, d50572, d324457, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40925 (p : Pattern) (guard : d221497 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 160 with
  | false =>
    have hg : d221496 p = 1 := by simpa only [d221497, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40924 p hg
    simpa only [d221497, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221497, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40610 p hg
    simpa only [d221497, d50576, d324458, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40926 (p : Pattern) (guard : d221498 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 159 with
  | false =>
    have hg : d221497 p = 1 := by simpa only [d221498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40925 p hg
    simpa only [d221498, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221498, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40593 p hg
    simpa only [d221498, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40927 (p : Pattern) (guard : d324894 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324889 p = 1 := by simpa only [d324894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40916 p hg
    simpa only [d324894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221498 p = 1 := by simpa only [d324894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40926 p hg
    simpa only [d324894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40928 (p : Pattern) (guard : d324895 p = 1) : d50576 p ≤ (0 : Int) + d324458 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324890 p = 1 := by simpa only [d324895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40917 p hg
    simpa only [d324895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324894 p = 1 := by simpa only [d324895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40927 p hg
    simpa only [d324895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40929 (p : Pattern) (guard : d324896 p = 1) : d50577 p ≤ (0 : Int) + d324459 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324896, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40592 p hg
    simpa only [d324896, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324895 p = 1 := by simpa only [d324896, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40928 p hg
    simpa only [d324896, d50577, d324459, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40930 (p : Pattern) (guard : d324897 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324897, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40591 p hg
    simpa only [d324897, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324896 p = 1 := by simpa only [d324897, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40929 p hg
    simpa only [d324897, d50578, d324460, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40931 (p : Pattern) (guard : d324898 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324893 p = 1 := by simpa only [d324898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40920 p hg
    simpa only [d324898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324897 p = 1 := by simpa only [d324898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40930 p hg
    simpa only [d324898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40932 (p : Pattern) (guard : d324899 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  cases selected : p 136 with
  | false =>
    have hg : d324897 p = 1 := by simpa only [d324899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40930 p hg
    simpa only [d324899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40644 p hg
    simpa only [d324899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40933 (p : Pattern) (guard : d324900 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324898 p = 1 := by simpa only [d324900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40931 p hg
    simpa only [d324900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324899 p = 1 := by simpa only [d324900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40932 p hg
    simpa only [d324900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40934 (p : Pattern) (guard : d324901 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324900 p = 1 := by simpa only [d324901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40933 p hg
    simpa only [d324901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40644 p hg
    simpa only [d324901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40935 (p : Pattern) (guard : d324902 p = 1) : d50590 p ≤ (0 : Int) + d324472 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324901 p = 1 := by simpa only [d324902, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40934 p hg
    simpa only [d324902, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324902, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40648 p hg
    simpa only [d324902, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40936 (p : Pattern) (guard : d324903 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324903, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40590 p hg
    simpa only [d324903, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324902 p = 1 := by simpa only [d324903, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40935 p hg
    simpa only [d324903, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40937 (p : Pattern) (guard : d324904 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  cases selected : p 135 with
  | false =>
    have hg : d324899 p = 1 := by simpa only [d324904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40932 p hg
    simpa only [d324904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40644 p hg
    simpa only [d324904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40938 (p : Pattern) (guard : d324905 p = 1) : d50578 p ≤ (0 : Int) + d324460 p := by
  cases selected : p 119 with
  | false =>
    have hg : d324904 p = 1 := by simpa only [d324905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40937 p hg
    simpa only [d324905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40644 p hg
    simpa only [d324905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40939 (p : Pattern) (guard : d324906 p = 1) : d50590 p ≤ (0 : Int) + d324472 p := by
  cases selected : p 116 with
  | false =>
    have hg : d324905 p = 1 := by simpa only [d324906, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40938 p hg
    simpa only [d324906, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324906, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40648 p hg
    simpa only [d324906, d50590, d324472, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40940 (p : Pattern) (guard : d324907 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324907, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40590 p hg
    simpa only [d324907, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324906 p = 1 := by simpa only [d324907, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40939 p hg
    simpa only [d324907, d50591, d324473, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40941 (p : Pattern) (guard : d324908 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324903 p = 1 := by simpa only [d324908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40936 p hg
    simpa only [d324908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324907 p = 1 := by simpa only [d324908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40940 p hg
    simpa only [d324908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40942 (p : Pattern) (guard : d324909 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324908 p = 1 := by simpa only [d324909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40941 p hg
    simpa only [d324909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40943 (p : Pattern) (guard : d324910 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324909 p = 1 := by simpa only [d324910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40942 p hg
    simpa only [d324910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40944 (p : Pattern) (guard : d324911 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324910 p = 1 := by simpa only [d324911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40943 p hg
    simpa only [d324911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40945 (p : Pattern) (guard : d324912 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 113 with
  | false =>
    have hg : d324907 p = 1 := by simpa only [d324912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40940 p hg
    simpa only [d324912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40946 (p : Pattern) (guard : d324913 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 96 with
  | false =>
    have hg : d324912 p = 1 := by simpa only [d324913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40945 p hg
    simpa only [d324913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40947 (p : Pattern) (guard : d324914 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 95 with
  | false =>
    have hg : d324913 p = 1 := by simpa only [d324914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40946 p hg
    simpa only [d324914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40948 (p : Pattern) (guard : d324915 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324914 p = 1 := by simpa only [d324915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40947 p hg
    simpa only [d324915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40949 (p : Pattern) (guard : d324916 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324911 p = 1 := by simpa only [d324916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40944 p hg
    simpa only [d324916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324915 p = 1 := by simpa only [d324916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40948 p hg
    simpa only [d324916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40950 (p : Pattern) (guard : d324917 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324916 p = 1 := by simpa only [d324917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40949 p hg
    simpa only [d324917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40951 (p : Pattern) (guard : d324918 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324917 p = 1 := by simpa only [d324918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40950 p hg
    simpa only [d324918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40952 (p : Pattern) (guard : d324919 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324918 p = 1 := by simpa only [d324919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40951 p hg
    simpa only [d324919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40953 (p : Pattern) (guard : d324920 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324919 p = 1 := by simpa only [d324920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40952 p hg
    simpa only [d324920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40954 (p : Pattern) (guard : d324921 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324920 p = 1 := by simpa only [d324921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40953 p hg
    simpa only [d324921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40955 (p : Pattern) (guard : d324924 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324910 p = 1 := by simpa only [d324924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40943 p hg
    simpa only [d324924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40956 (p : Pattern) (guard : d324925 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 93 with
  | false =>
    have hg : d324914 p = 1 := by simpa only [d324925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40947 p hg
    simpa only [d324925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40957 (p : Pattern) (guard : d324926 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 91 with
  | false =>
    have hg : d324924 p = 1 := by simpa only [d324926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40955 p hg
    simpa only [d324926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324925 p = 1 := by simpa only [d324926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40956 p hg
    simpa only [d324926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40958 (p : Pattern) (guard : d324927 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324926 p = 1 := by simpa only [d324927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40957 p hg
    simpa only [d324927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40959 (p : Pattern) (guard : d324928 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 89 with
  | false =>
    have hg : d324927 p = 1 := by simpa only [d324928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40958 p hg
    simpa only [d324928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40960 (p : Pattern) (guard : d324929 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324928 p = 1 := by simpa only [d324929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40959 p hg
    simpa only [d324929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40961 (p : Pattern) (guard : d324930 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324929 p = 1 := by simpa only [d324930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40960 p hg
    simpa only [d324930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40962 (p : Pattern) (guard : d324931 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 71 with
  | false =>
    have hg : d324920 p = 1 := by simpa only [d324931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40953 p hg
    simpa only [d324931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324930 p = 1 := by simpa only [d324931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40961 p hg
    simpa only [d324931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40963 (p : Pattern) (guard : d324932 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 70 with
  | false =>
    have hg : d324921 p = 1 := by simpa only [d324932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40954 p hg
    simpa only [d324932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324931 p = 1 := by simpa only [d324932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40962 p hg
    simpa only [d324932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40964 (p : Pattern) (guard : d324933 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 69 with
  | false =>
    have hg : d324932 p = 1 := by simpa only [d324933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40963 p hg
    simpa only [d324933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d324933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40965 (p : Pattern) (guard : d325209 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 51 with
  | false =>
    have hg : d324933 p = 1 := by simpa only [d325209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40964 p hg
    simpa only [d325209, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d325209, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d325209, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40966 (p : Pattern) (guard : d325210 p = 1) : d50591 p ≤ (0 : Int) + d324473 p := by
  cases selected : p 50 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d325210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40589 p hg
    simpa only [d325210, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d325209 p = 1 := by simpa only [d325210, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40965 p hg
    simpa only [d325210, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40967 (p : Pattern) (guard : d10055 p = 1) : d49565 p ≤ (0 : Int) + d49565 p := by
  omega
theorem compare40968 (p : Pattern) (guard : d38167 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38167, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40689 p hg
    simpa only [d38167, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10055 p = 1 := by simpa only [d38167, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40967 p hg
    simpa only [d38167, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40969 (p : Pattern) (guard : d38168 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d38167 p = 1 := by simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40968 p hg
    simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40692 p hg
    simpa only [d38168, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40970 (p : Pattern) (guard : d38169 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d38168 p = 1 := by simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40969 p hg
    simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40692 p hg
    simpa only [d38169, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40971 (p : Pattern) (guard : d38170 p = 1) : d50642 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 182 with
  | false =>
    have hg : d38169 p = 1 := by simpa only [d38170, d50642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40970 p hg
    simpa only [d38170, d50642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38170, d50642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40695 p hg
    simpa only [d38170, d50642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40972 (p : Pattern) (guard : d38177 p = 1) : d50642 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40688 p hg
    simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38170 p = 1 := by simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40971 p hg
    simpa only [d38177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40973 (p : Pattern) (guard : d38178 p = 1) : d50657 p ≤ (0 : Int) + d324503 p := by
  cases selected : p 163 with
  | false =>
    have hg : d38177 p = 1 := by simpa only [d38178, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40972 p hg
    simpa only [d38178, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38178, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40698 p hg
    simpa only [d38178, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40974 (p : Pattern) (guard : d38179 p = 1) : d50658 p ≤ (0 : Int) + d324504 p := by
  cases selected : p 162 with
  | false =>
    have hg : d38178 p = 1 := by simpa only [d38179, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40973 p hg
    simpa only [d38179, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38179, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d38179, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40975 (p : Pattern) (guard : d38180 p = 1) : d50659 p ≤ (0 : Int) + d324505 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38180, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40687 p hg
    simpa only [d38180, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38179 p = 1 := by simpa only [d38180, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40974 p hg
    simpa only [d38180, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40976 (p : Pattern) (guard : d38181 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d38180 p = 1 := by simpa only [d38181, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40975 p hg
    simpa only [d38181, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d38181, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40702 p hg
    simpa only [d38181, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40977 (p : Pattern) (guard : d38302 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d38302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40686 p hg
    simpa only [d38302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d38181 p = 1 := by simpa only [d38302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40976 p hg
    simpa only [d38302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40978 (p : Pattern) (guard : d2043 p = 1) : d49565 p ≤ (0 : Int) + d49565 p := by
  omega
theorem compare40979 (p : Pattern) (guard : d221468 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221468, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40689 p hg
    simpa only [d221468, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d221468, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40978 p hg
    simpa only [d221468, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40980 (p : Pattern) (guard : d221488 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221468 p = 1 := by simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40979 p hg
    simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40692 p hg
    simpa only [d221488, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40981 (p : Pattern) (guard : d10406 p = 1) : d49565 p ≤ (0 : Int) + d49565 p := by
  omega
theorem compare40982 (p : Pattern) (guard : d221489 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 204 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d221489, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40689 p hg
    simpa only [d221489, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d10406 p = 1 := by simpa only [d221489, d50606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40981 p hg
    simpa only [d221489, d50606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40983 (p : Pattern) (guard : d221490 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 202 with
  | false =>
    have hg : d221489 p = 1 := by simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40982 p hg
    simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40692 p hg
    simpa only [d221490, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40984 (p : Pattern) (guard : d221491 p = 1) : d50606 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 201 with
  | false =>
    have hg : d221488 p = 1 := by simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40980 p hg
    simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221490 p = 1 := by simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40983 p hg
    simpa only [d221491, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40985 (p : Pattern) (guard : d221492 p = 1) : d50642 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 182 with
  | false =>
    have hg : d221491 p = 1 := by simpa only [d221492, d50642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40984 p hg
    simpa only [d221492, d50642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221492, d50642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40695 p hg
    simpa only [d221492, d50642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40986 (p : Pattern) (guard : d324882 p = 1) : d50642 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 180 with
  | false =>
    have hg : d38170 p = 1 := by simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40971 p hg
    simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d221492 p = 1 := by simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40985 p hg
    simpa only [d324882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40987 (p : Pattern) (guard : d324883 p = 1) : d50657 p ≤ (0 : Int) + d324503 p := by
  cases selected : p 163 with
  | false =>
    have hg : d324882 p = 1 := by simpa only [d324883, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40986 p hg
    simpa only [d324883, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324883, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40698 p hg
    simpa only [d324883, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40988 (p : Pattern) (guard : d324884 p = 1) : d50658 p ≤ (0 : Int) + d324504 p := by
  cases selected : p 162 with
  | false =>
    have hg : d324883 p = 1 := by simpa only [d324884, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40987 p hg
    simpa only [d324884, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324884, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare100 p hg
    simpa only [d324884, d50658, d324504, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40989 (p : Pattern) (guard : d324885 p = 1) : d50659 p ≤ (0 : Int) + d324505 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324885, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40687 p hg
    simpa only [d324885, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324884 p = 1 := by simpa only [d324885, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40988 p hg
    simpa only [d324885, d50659, d324505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40990 (p : Pattern) (guard : d324886 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 160 with
  | false =>
    have hg : d324885 p = 1 := by simpa only [d324886, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40989 p hg
    simpa only [d324886, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324886, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40702 p hg
    simpa only [d324886, d50663, d324506, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40991 (p : Pattern) (guard : d324887 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d38181 p = 1 := by simpa only [d324887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40976 p hg
    simpa only [d324887, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324886 p = 1 := by simpa only [d324887, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40990 p hg
    simpa only [d324887, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40992 (p : Pattern) (guard : d324888 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d38302 p = 1 := by simpa only [d324888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40977 p hg
    simpa only [d324888, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324887 p = 1 := by simpa only [d324888, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40991 p hg
    simpa only [d324888, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40993 (p : Pattern) (guard : d324889 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 159 with
  | false =>
    have hg : d324886 p = 1 := by simpa only [d324889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40990 p hg
    simpa only [d324889, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d324889, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40686 p hg
    simpa only [d324889, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40994 (p : Pattern) (guard : d324890 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 158 with
  | false =>
    have hg : d324887 p = 1 := by simpa only [d324890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40991 p hg
    simpa only [d324890, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324889 p = 1 := by simpa only [d324890, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40993 p hg
    simpa only [d324890, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40995 (p : Pattern) (guard : d324891 p = 1) : d50663 p ≤ (0 : Int) + d324506 p := by
  cases selected : p 157 with
  | false =>
    have hg : d324888 p = 1 := by simpa only [d324891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40992 p hg
    simpa only [d324891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324890 p = 1 := by simpa only [d324891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40994 p hg
    simpa only [d324891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40996 (p : Pattern) (guard : d324892 p = 1) : d50664 p ≤ (0 : Int) + d324507 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324892, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40685 p hg
    simpa only [d324892, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324891 p = 1 := by simpa only [d324892, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40995 p hg
    simpa only [d324892, d50664, d324507, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40997 (p : Pattern) (guard : d324893 p = 1) : d50665 p ≤ (0 : Int) + d324508 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d324893, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40684 p hg
    simpa only [d324893, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d324892 p = 1 := by simpa only [d324893, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40996 p hg
    simpa only [d324893, d50665, d324508, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40998 (p : Pattern) (guard : d221493 p = 1) : d50642 p ≤ (0 : Int) + d49565 p := by
  cases selected : p 180 with
  | false =>
    have hg : d221492 p = 1 := by simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40985 p hg
    simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40688 p hg
    simpa only [d221493, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare40999 (p : Pattern) (guard : d221494 p = 1) : d50657 p ≤ (0 : Int) + d324503 p := by
  cases selected : p 163 with
  | false =>
    have hg : d221493 p = 1 := by simpa only [d221494, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40998 p hg
    simpa only [d221494, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d221494, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare40698 p hg
    simpa only [d221494, d50657, d324503, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
