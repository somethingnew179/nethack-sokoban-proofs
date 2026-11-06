import NetHack.Soko22Hazard87.Compare198
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare49750 (p : Pattern) (guard : d326588 p = 1) : d50733 p ≤ (0 : Int) + d371255 p := by
  cases selected : p 157 with
  | false =>
    have hg : d47096 p = 1 := by simpa only [d326588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49695 p hg
    simpa only [d326588, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326587 p = 1 := by simpa only [d326588, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49749 p hg
    simpa only [d326588, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49751 (p : Pattern) (guard : d326589 p = 1) : d50734 p ≤ (0 : Int) + d371256 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326589, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49637 p hg
    simpa only [d326589, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326588 p = 1 := by simpa only [d326589, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49750 p hg
    simpa only [d326589, d50734, d371256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49752 (p : Pattern) (guard : d326590 p = 1) : d50735 p ≤ (0 : Int) + d371257 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326590, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49636 p hg
    simpa only [d326590, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326589 p = 1 := by simpa only [d326590, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49751 p hg
    simpa only [d326590, d50735, d371257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49753 (p : Pattern) (guard : d326591 p = 1) : d50735 p ≤ (0 : Int) + d371257 p := by
  cases selected : p 136 with
  | false =>
    have hg : d326590 p = 1 := by simpa only [d326591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49752 p hg
    simpa only [d326591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49714 p hg
    simpa only [d326591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49754 (p : Pattern) (guard : d326592 p = 1) : d50735 p ≤ (0 : Int) + d371257 p := by
  cases selected : p 135 with
  | false =>
    have hg : d326591 p = 1 := by simpa only [d326592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49753 p hg
    simpa only [d326592, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326592, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49714 p hg
    simpa only [d326592, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49755 (p : Pattern) (guard : d326593 p = 1) : d50735 p ≤ (0 : Int) + d371257 p := by
  cases selected : p 119 with
  | false =>
    have hg : d326592 p = 1 := by simpa only [d326593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49754 p hg
    simpa only [d326593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49714 p hg
    simpa only [d326593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49756 (p : Pattern) (guard : d326594 p = 1) : d50737 p ≤ (0 : Int) + d371259 p := by
  cases selected : p 116 with
  | false =>
    have hg : d326593 p = 1 := by simpa only [d326594, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49755 p hg
    simpa only [d326594, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326594, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49718 p hg
    simpa only [d326594, d50737, d371259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49757 (p : Pattern) (guard : d326595 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326595, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49462 p hg
    simpa only [d326595, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326594 p = 1 := by simpa only [d326595, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49756 p hg
    simpa only [d326595, d50738, d371260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49758 (p : Pattern) (guard : d326596 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  cases selected : p 113 with
  | false =>
    have hg : d326595 p = 1 := by simpa only [d326596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49757 p hg
    simpa only [d326596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49635 p hg
    simpa only [d326596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49759 (p : Pattern) (guard : d326597 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  cases selected : p 96 with
  | false =>
    have hg : d326596 p = 1 := by simpa only [d326597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49758 p hg
    simpa only [d326597, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326597, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49635 p hg
    simpa only [d326597, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49760 (p : Pattern) (guard : d326598 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  cases selected : p 95 with
  | false =>
    have hg : d326597 p = 1 := by simpa only [d326598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49759 p hg
    simpa only [d326598, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326598, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49635 p hg
    simpa only [d326598, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49761 (p : Pattern) (guard : d326599 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  cases selected : p 93 with
  | false =>
    have hg : d326598 p = 1 := by simpa only [d326599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49760 p hg
    simpa only [d326599, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326599, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49635 p hg
    simpa only [d326599, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49762 (p : Pattern) (guard : d326600 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  cases selected : p 91 with
  | false =>
    have hg : d47131 p = 1 := by simpa only [d326600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49728 p hg
    simpa only [d326600, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326599 p = 1 := by simpa only [d326600, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49761 p hg
    simpa only [d326600, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49763 (p : Pattern) (guard : d326601 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49635 p hg
    simpa only [d326601, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326600 p = 1 := by simpa only [d326601, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49762 p hg
    simpa only [d326601, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49764 (p : Pattern) (guard : d326602 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  cases selected : p 89 with
  | false =>
    have hg : d326601 p = 1 := by simpa only [d326602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49763 p hg
    simpa only [d326602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49635 p hg
    simpa only [d326602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49765 (p : Pattern) (guard : d326603 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49635 p hg
    simpa only [d326603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326602 p = 1 := by simpa only [d326603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49764 p hg
    simpa only [d326603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49766 (p : Pattern) (guard : d326604 p = 1) : d50738 p ≤ (0 : Int) + d371260 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49635 p hg
    simpa only [d326604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326603 p = 1 := by simpa only [d326604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49765 p hg
    simpa only [d326604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49767 (p : Pattern) (guard : d326605 p = 1) : d50739 p ≤ (0 : Int) + d371261 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326605, d50739, d371261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49461 p hg
    simpa only [d326605, d50739, d371261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326604 p = 1 := by simpa only [d326605, d50739, d371261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49766 p hg
    simpa only [d326605, d50739, d371261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49768 (p : Pattern) (guard : d326606 p = 1) : d50739 p ≤ (0 : Int) + d371261 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49634 p hg
    simpa only [d326606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326605 p = 1 := by simpa only [d326606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49767 p hg
    simpa only [d326606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49769 (p : Pattern) (guard : d326607 p = 1) : d50739 p ≤ (0 : Int) + d371261 p := by
  cases selected : p 69 with
  | false =>
    have hg : d326606 p = 1 := by simpa only [d326607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49768 p hg
    simpa only [d326607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49634 p hg
    simpa only [d326607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49770 (p : Pattern) (guard : d326608 p = 1) : d50739 p ≤ (0 : Int) + d371261 p := by
  cases selected : p 51 with
  | false =>
    have hg : d326607 p = 1 := by simpa only [d326608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49769 p hg
    simpa only [d326608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49634 p hg
    simpa only [d326608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49771 (p : Pattern) (guard : d326609 p = 1) : d50739 p ≤ (0 : Int) + d371261 p := by
  cases selected : p 50 with
  | false =>
    have hg : d326608 p = 1 := by simpa only [d326609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49770 p hg
    simpa only [d326609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49634 p hg
    simpa only [d326609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49772 (p : Pattern) (guard : d0 p = 1) : d50821 p ≤ (0 : Int) + d371351 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49773 (p : Pattern) (guard : d326610 p = 1) : d50822 p ≤ (0 : Int) + d371352 p := by
  cases selected : p 49 with
  | false =>
    have hg : d326609 p = 1 := by simpa only [d326610, d50822, d371352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49771 p hg
    simpa only [d326610, d50822, d371352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d326610, d50822, d371352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49772 p hg
    simpa only [d326610, d50822, d371352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49774 (p : Pattern) (guard : d326611 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 48 with
  | false =>
    have hg : d321915 p = 1 := by simpa only [d326611, d50823, d371353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49633 p hg
    simpa only [d326611, d50823, d371353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326610 p = 1 := by simpa only [d326611, d50823, d371353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49773 p hg
    simpa only [d326611, d50823, d371353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49775 (p : Pattern) (guard : d326612 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d326612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326611 p = 1 := by simpa only [d326612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49774 p hg
    simpa only [d326612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49776 (p : Pattern) (guard : d326613 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d326613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326612 p = 1 := by simpa only [d326613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49775 p hg
    simpa only [d326613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49777 (p : Pattern) (guard : d326614 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d326614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326613 p = 1 := by simpa only [d326614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49776 p hg
    simpa only [d326614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49778 (p : Pattern) (guard : d326615 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d326615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326614 p = 1 := by simpa only [d326615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49777 p hg
    simpa only [d326615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49779 (p : Pattern) (guard : d326616 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d326616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326615 p = 1 := by simpa only [d326616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49778 p hg
    simpa only [d326616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49780 (p : Pattern) (guard : d326617 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d326617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326616 p = 1 := by simpa only [d326617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49779 p hg
    simpa only [d326617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49781 (p : Pattern) (guard : d326618 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d326618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326617 p = 1 := by simpa only [d326618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49780 p hg
    simpa only [d326618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49782 (p : Pattern) (guard : d326619 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d326619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326618 p = 1 := by simpa only [d326619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49781 p hg
    simpa only [d326619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49783 (p : Pattern) (guard : d326620 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d326620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326619 p = 1 := by simpa only [d326620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49782 p hg
    simpa only [d326620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49784 (p : Pattern) (guard : d326621 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d326621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d326621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326620 p = 1 := by simpa only [d326621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49783 p hg
    simpa only [d326621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49785 (p : Pattern) (guard : d375297 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d375297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375297, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d326621 p = 1 := by simpa only [d375297, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49784 p hg
    simpa only [d375297, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49786 (p : Pattern) (guard : d375298 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 260 with
  | false =>
    have hg : d375297 p = 1 := by simpa only [d375298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49785 p hg
    simpa only [d375298, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375298, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375298, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49787 (p : Pattern) (guard : d375299 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 259 with
  | false =>
    have hg : d375298 p = 1 := by simpa only [d375299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49786 p hg
    simpa only [d375299, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375299, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375299, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49788 (p : Pattern) (guard : d375300 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 258 with
  | false =>
    have hg : d375299 p = 1 := by simpa only [d375300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49787 p hg
    simpa only [d375300, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375300, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375300, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49789 (p : Pattern) (guard : d375301 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 257 with
  | false =>
    have hg : d375300 p = 1 := by simpa only [d375301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49788 p hg
    simpa only [d375301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49790 (p : Pattern) (guard : d375302 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 256 with
  | false =>
    have hg : d375301 p = 1 := by simpa only [d375302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49789 p hg
    simpa only [d375302, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375302, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375302, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49791 (p : Pattern) (guard : d375303 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 255 with
  | false =>
    have hg : d375302 p = 1 := by simpa only [d375303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49790 p hg
    simpa only [d375303, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375303, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375303, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49792 (p : Pattern) (guard : d375304 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 254 with
  | false =>
    have hg : d375303 p = 1 := by simpa only [d375304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49791 p hg
    simpa only [d375304, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375304, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375304, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49793 (p : Pattern) (guard : d375305 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 253 with
  | false =>
    have hg : d375304 p = 1 := by simpa only [d375305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49792 p hg
    simpa only [d375305, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375305, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375305, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49794 (p : Pattern) (guard : d375306 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 252 with
  | false =>
    have hg : d375305 p = 1 := by simpa only [d375306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49793 p hg
    simpa only [d375306, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375306, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375306, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49795 (p : Pattern) (guard : d375307 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 251 with
  | false =>
    have hg : d375306 p = 1 := by simpa only [d375307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49794 p hg
    simpa only [d375307, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375307, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375307, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49796 (p : Pattern) (guard : d375308 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 250 with
  | false =>
    have hg : d375307 p = 1 := by simpa only [d375308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49795 p hg
    simpa only [d375308, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375308, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375308, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49797 (p : Pattern) (guard : d375309 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 249 with
  | false =>
    have hg : d375308 p = 1 := by simpa only [d375309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49796 p hg
    simpa only [d375309, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375309, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375309, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49798 (p : Pattern) (guard : d375310 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 245 with
  | false =>
    have hg : d375309 p = 1 := by simpa only [d375310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49797 p hg
    simpa only [d375310, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375310, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375310, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49799 (p : Pattern) (guard : d375311 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 200 with
  | false =>
    have hg : d375310 p = 1 := by simpa only [d375311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49798 p hg
    simpa only [d375311, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375311, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375311, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49800 (p : Pattern) (guard : d375312 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 199 with
  | false =>
    have hg : d375311 p = 1 := by simpa only [d375312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49799 p hg
    simpa only [d375312, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375312, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375312, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49801 (p : Pattern) (guard : d375313 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 186 with
  | false =>
    have hg : d375312 p = 1 := by simpa only [d375313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49800 p hg
    simpa only [d375313, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375313, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375313, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49802 (p : Pattern) (guard : d375314 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 185 with
  | false =>
    have hg : d375313 p = 1 := by simpa only [d375314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49801 p hg
    simpa only [d375314, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375314, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375314, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49803 (p : Pattern) (guard : d375315 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 184 with
  | false =>
    have hg : d375314 p = 1 := by simpa only [d375315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49802 p hg
    simpa only [d375315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49804 (p : Pattern) (guard : d375316 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 181 with
  | false =>
    have hg : d375315 p = 1 := by simpa only [d375316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49803 p hg
    simpa only [d375316, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375316, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375316, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49805 (p : Pattern) (guard : d375317 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 177 with
  | false =>
    have hg : d375316 p = 1 := by simpa only [d375317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49804 p hg
    simpa only [d375317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49806 (p : Pattern) (guard : d375318 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 164 with
  | false =>
    have hg : d375317 p = 1 := by simpa only [d375318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49805 p hg
    simpa only [d375318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49807 (p : Pattern) (guard : d375319 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 156 with
  | false =>
    have hg : d375318 p = 1 := by simpa only [d375319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49806 p hg
    simpa only [d375319, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375319, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375319, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49808 (p : Pattern) (guard : d375320 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 155 with
  | false =>
    have hg : d375319 p = 1 := by simpa only [d375320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49807 p hg
    simpa only [d375320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49809 (p : Pattern) (guard : d375321 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 134 with
  | false =>
    have hg : d375320 p = 1 := by simpa only [d375321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49808 p hg
    simpa only [d375321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49810 (p : Pattern) (guard : d375322 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 133 with
  | false =>
    have hg : d375321 p = 1 := by simpa only [d375322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49809 p hg
    simpa only [d375322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49811 (p : Pattern) (guard : d375323 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 120 with
  | false =>
    have hg : d375322 p = 1 := by simpa only [d375323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49810 p hg
    simpa only [d375323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49812 (p : Pattern) (guard : d375324 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 118 with
  | false =>
    have hg : d375323 p = 1 := by simpa only [d375324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49811 p hg
    simpa only [d375324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49813 (p : Pattern) (guard : d375325 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 114 with
  | false =>
    have hg : d375324 p = 1 := by simpa only [d375325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49812 p hg
    simpa only [d375325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49814 (p : Pattern) (guard : d375326 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 111 with
  | false =>
    have hg : d375325 p = 1 := by simpa only [d375326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49813 p hg
    simpa only [d375326, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375326, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375326, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49815 (p : Pattern) (guard : d375327 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 98 with
  | false =>
    have hg : d375326 p = 1 := by simpa only [d375327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49814 p hg
    simpa only [d375327, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375327, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375327, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49816 (p : Pattern) (guard : d375328 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 97 with
  | false =>
    have hg : d375327 p = 1 := by simpa only [d375328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49815 p hg
    simpa only [d375328, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375328, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375328, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49817 (p : Pattern) (guard : d375329 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 94 with
  | false =>
    have hg : d375328 p = 1 := by simpa only [d375329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49816 p hg
    simpa only [d375329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49818 (p : Pattern) (guard : d375330 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 76 with
  | false =>
    have hg : d375329 p = 1 := by simpa only [d375330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49817 p hg
    simpa only [d375330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49819 (p : Pattern) (guard : d375331 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 67 with
  | false =>
    have hg : d375330 p = 1 := by simpa only [d375331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49818 p hg
    simpa only [d375331, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375331, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375331, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49820 (p : Pattern) (guard : d375332 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 52 with
  | false =>
    have hg : d375331 p = 1 := by simpa only [d375332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49819 p hg
    simpa only [d375332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49821 (p : Pattern) (guard : d375333 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 47 with
  | false =>
    have hg : d375332 p = 1 := by simpa only [d375333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49820 p hg
    simpa only [d375333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49822 (p : Pattern) (guard : d375334 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 46 with
  | false =>
    have hg : d375333 p = 1 := by simpa only [d375334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49821 p hg
    simpa only [d375334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49823 (p : Pattern) (guard : d375335 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 45 with
  | false =>
    have hg : d375334 p = 1 := by simpa only [d375335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49822 p hg
    simpa only [d375335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49824 (p : Pattern) (guard : d375336 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 30 with
  | false =>
    have hg : d375335 p = 1 := by simpa only [d375336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49823 p hg
    simpa only [d375336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49825 (p : Pattern) (guard : d375337 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 29 with
  | false =>
    have hg : d375336 p = 1 := by simpa only [d375337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49824 p hg
    simpa only [d375337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49826 (p : Pattern) (guard : d375338 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 28 with
  | false =>
    have hg : d375337 p = 1 := by simpa only [d375338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49825 p hg
    simpa only [d375338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49827 (p : Pattern) (guard : d375339 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 27 with
  | false =>
    have hg : d375338 p = 1 := by simpa only [d375339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49826 p hg
    simpa only [d375339, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375339, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375339, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49828 (p : Pattern) (guard : d375340 p = 1) : d50823 p ≤ (0 : Int) + d371353 p := by
  cases selected : p 25 with
  | false =>
    have hg : d375339 p = 1 := by simpa only [d375340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49827 p hg
    simpa only [d375340, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d375340, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare49460 p hg
    simpa only [d375340, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare49829 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (0 : Int) + d50823 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49830 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (1 : Int) + d376289 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49831 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (0 : Int) + d376289 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49832 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (11 : Int) + d50823 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare49833 (p : Pattern) (guard : d0 p = 1) : d50823 p ≤ (10 : Int) + d50823 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Soko22Hazard87
