import NetHack.Soko22Hazard87.Compare126
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare31750 (p : Pattern) (guard : d259602 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259591 p = 1 := by simpa only [d259602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31739 p hg
    simpa only [d259602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d259602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31751 (p : Pattern) (guard : d259603 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259601 p = 1 := by simpa only [d259603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31749 p hg
    simpa only [d259603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259602 p = 1 := by simpa only [d259603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31750 p hg
    simpa only [d259603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31752 (p : Pattern) (guard : d259604 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259593 p = 1 := by simpa only [d259604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31741 p hg
    simpa only [d259604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259603 p = 1 := by simpa only [d259604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31751 p hg
    simpa only [d259604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31753 (p : Pattern) (guard : d259605 p = 1) : d47756 p ≤ (-2 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259605, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30834 p hg
    simpa only [d259605, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259604 p = 1 := by simpa only [d259605, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31752 p hg
    simpa only [d259605, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31754 (p : Pattern) (guard : d259606 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259606, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30833 p hg
    simpa only [d259606, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259605 p = 1 := by simpa only [d259606, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31753 p hg
    simpa only [d259606, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31755 (p : Pattern) (guard : d259607 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259600 p = 1 := by simpa only [d259607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31748 p hg
    simpa only [d259607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d259607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31756 (p : Pattern) (guard : d259608 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259607 p = 1 := by simpa only [d259608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31755 p hg
    simpa only [d259608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30858 p hg
    simpa only [d259608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31757 (p : Pattern) (guard : d259609 p = 1) : d47755 p ≤ (-2 : Int) + d253394 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259603 p = 1 := by simpa only [d259609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31751 p hg
    simpa only [d259609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259608 p = 1 := by simpa only [d259609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31756 p hg
    simpa only [d259609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31758 (p : Pattern) (guard : d259610 p = 1) : d47756 p ≤ (-2 : Int) + d253395 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259610, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30834 p hg
    simpa only [d259610, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259609 p = 1 := by simpa only [d259610, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31757 p hg
    simpa only [d259610, d47756, d253395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31759 (p : Pattern) (guard : d259611 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259611, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30833 p hg
    simpa only [d259611, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259610 p = 1 := by simpa only [d259611, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31758 p hg
    simpa only [d259611, d47757, d253396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31760 (p : Pattern) (guard : d259612 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259606 p = 1 := by simpa only [d259612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31754 p hg
    simpa only [d259612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259611 p = 1 := by simpa only [d259612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31759 p hg
    simpa only [d259612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31761 (p : Pattern) (guard : d259613 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259611 p = 1 := by simpa only [d259613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31759 p hg
    simpa only [d259613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d259613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31762 (p : Pattern) (guard : d259614 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259612 p = 1 := by simpa only [d259614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31760 p hg
    simpa only [d259614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259613 p = 1 := by simpa only [d259614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31761 p hg
    simpa only [d259614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31763 (p : Pattern) (guard : d259615 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259614 p = 1 := by simpa only [d259615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31762 p hg
    simpa only [d259615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d259615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31764 (p : Pattern) (guard : d259616 p = 1) : d47765 p ≤ (-2 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259615 p = 1 := by simpa only [d259616, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31763 p hg
    simpa only [d259616, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259616, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30868 p hg
    simpa only [d259616, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31765 (p : Pattern) (guard : d259617 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259617, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30832 p hg
    simpa only [d259617, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259616 p = 1 := by simpa only [d259617, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31764 p hg
    simpa only [d259617, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31766 (p : Pattern) (guard : d259618 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259613 p = 1 := by simpa only [d259618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31761 p hg
    simpa only [d259618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d259618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31767 (p : Pattern) (guard : d259619 p = 1) : d47757 p ≤ (-2 : Int) + d253396 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259618 p = 1 := by simpa only [d259619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31766 p hg
    simpa only [d259619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30864 p hg
    simpa only [d259619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31768 (p : Pattern) (guard : d259620 p = 1) : d47765 p ≤ (-2 : Int) + d253404 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259619 p = 1 := by simpa only [d259620, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31767 p hg
    simpa only [d259620, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259620, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30868 p hg
    simpa only [d259620, d47765, d253404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31769 (p : Pattern) (guard : d259621 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259621, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30832 p hg
    simpa only [d259621, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259620 p = 1 := by simpa only [d259621, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31768 p hg
    simpa only [d259621, d47766, d253405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31770 (p : Pattern) (guard : d259622 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259617 p = 1 := by simpa only [d259622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31765 p hg
    simpa only [d259622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259621 p = 1 := by simpa only [d259622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31769 p hg
    simpa only [d259622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31771 (p : Pattern) (guard : d259623 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259622 p = 1 := by simpa only [d259623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31770 p hg
    simpa only [d259623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31772 (p : Pattern) (guard : d259624 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259623 p = 1 := by simpa only [d259624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31771 p hg
    simpa only [d259624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31773 (p : Pattern) (guard : d259638 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259624 p = 1 := by simpa only [d259638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31772 p hg
    simpa only [d259638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31774 (p : Pattern) (guard : d259626 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259621 p = 1 := by simpa only [d259626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31769 p hg
    simpa only [d259626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31775 (p : Pattern) (guard : d259627 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259626 p = 1 := by simpa only [d259627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31774 p hg
    simpa only [d259627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31776 (p : Pattern) (guard : d259628 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259627 p = 1 := by simpa only [d259628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31775 p hg
    simpa only [d259628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31777 (p : Pattern) (guard : d259639 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259628 p = 1 := by simpa only [d259639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31776 p hg
    simpa only [d259639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31778 (p : Pattern) (guard : d259640 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259638 p = 1 := by simpa only [d259640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31773 p hg
    simpa only [d259640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259639 p = 1 := by simpa only [d259640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31777 p hg
    simpa only [d259640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31779 (p : Pattern) (guard : d259641 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259640 p = 1 := by simpa only [d259641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31778 p hg
    simpa only [d259641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31780 (p : Pattern) (guard : d259642 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 89 with
  | false =>
    have hg : d259641 p = 1 := by simpa only [d259642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31779 p hg
    simpa only [d259642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31781 (p : Pattern) (guard : d259643 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259642 p = 1 := by simpa only [d259643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31780 p hg
    simpa only [d259643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31782 (p : Pattern) (guard : d259644 p = 1) : d47766 p ≤ (-2 : Int) + d253405 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30831 p hg
    simpa only [d259644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259643 p = 1 := by simpa only [d259644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31781 p hg
    simpa only [d259644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31783 (p : Pattern) (guard : d260193 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260193, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260193, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259644 p = 1 := by simpa only [d260193, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31782 p hg
    simpa only [d260193, d47767, d253406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31784 (p : Pattern) (guard : d260194 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260194, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260193 p = 1 := by simpa only [d260194, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31783 p hg
    simpa only [d260194, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31785 (p : Pattern) (guard : d260195 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 69 with
  | false =>
    have hg : d260194 p = 1 := by simpa only [d260195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31784 p hg
    simpa only [d260195, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260195, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260195, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31786 (p : Pattern) (guard : d260196 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 51 with
  | false =>
    have hg : d260195 p = 1 := by simpa only [d260196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31785 p hg
    simpa only [d260196, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260196, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260196, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31787 (p : Pattern) (guard : d260197 p = 1) : d47767 p ≤ (-2 : Int) + d253406 p := by
  cases selected : p 50 with
  | false =>
    have hg : d260196 p = 1 := by simpa only [d260197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31786 p hg
    simpa only [d260197, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260197, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30830 p hg
    simpa only [d260197, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31788 (p : Pattern) (guard : d260198 p = 1) : d47768 p ≤ (-2 : Int) + d253407 p := by
  cases selected : p 49 with
  | false =>
    have hg : d260192 p = 1 := by simpa only [d260198, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31713 p hg
    simpa only [d260198, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260197 p = 1 := by simpa only [d260198, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31787 p hg
    simpa only [d260198, d47768, d253407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31789 (p : Pattern) (guard : d258183 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257870 p = 1 := by simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31499 p hg
    simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31790 (p : Pattern) (guard : d258184 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258183 p = 1 := by simpa only [d258184, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31789 p hg
    simpa only [d258184, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258184, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30903 p hg
    simpa only [d258184, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31791 (p : Pattern) (guard : d258185 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258184 p = 1 := by simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31790 p hg
    simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31792 (p : Pattern) (guard : d258274 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d258274, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258185 p = 1 := by simpa only [d258274, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31791 p hg
    simpa only [d258274, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31793 (p : Pattern) (guard : d258186 p = 1) : d47797 p ≤ (-2 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258185 p = 1 := by simpa only [d258186, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31634 p hg
    simpa only [d258186, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258186, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d258186, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31794 (p : Pattern) (guard : d258275 p = 1) : d47798 p ≤ (-2 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258274 p = 1 := by simpa only [d258275, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31792 p hg
    simpa only [d258275, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258186 p = 1 := by simpa only [d258275, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31793 p hg
    simpa only [d258275, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31795 (p : Pattern) (guard : d258183 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d257870 p = 1 := by simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31518 p hg
    simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d258183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31796 (p : Pattern) (guard : d258184 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d258183 p = 1 := by simpa only [d258184, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31795 p hg
    simpa only [d258184, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258184, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30921 p hg
    simpa only [d258184, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31797 (p : Pattern) (guard : d258185 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30923 p hg
    simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258184 p = 1 := by simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31796 p hg
    simpa only [d258185, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31798 (p : Pattern) (guard : d258186 p = 1) : d47682 p ≤ (-2 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d258185 p = 1 := by simpa only [d258186, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31797 p hg
    simpa only [d258186, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258186, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d258186, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31799 (p : Pattern) (guard : d258187 p = 1) : d47683 p ≤ (-2 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d258186 p = 1 := by simpa only [d258187, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31798 p hg
    simpa only [d258187, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258187, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d258187, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31800 (p : Pattern) (guard : d258276 p = 1) : d47799 p ≤ (-2 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d258275 p = 1 := by simpa only [d258276, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31794 p hg
    simpa only [d258276, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258187 p = 1 := by simpa only [d258276, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31799 p hg
    simpa only [d258276, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31801 (p : Pattern) (guard : d258277 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d258276 p = 1 := by simpa only [d258277, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31800 p hg
    simpa only [d258277, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d258277, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d258277, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31802 (p : Pattern) (guard : d259573 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 225 with
  | false =>
    have hg : d258806 p = 1 := by simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31055 p hg
    simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31803 (p : Pattern) (guard : d259574 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259573 p = 1 := by simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31802 p hg
    simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31804 (p : Pattern) (guard : d259575 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31502 p hg
    simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259574 p = 1 := by simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31803 p hg
    simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31805 (p : Pattern) (guard : d259576 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258695 p = 1 := by simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30898 p hg
    simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31806 (p : Pattern) (guard : d259577 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 204 with
  | false =>
    have hg : d259575 p = 1 := by simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31804 p hg
    simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259576 p = 1 := by simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31805 p hg
    simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31807 (p : Pattern) (guard : d259578 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 202 with
  | false =>
    have hg : d259577 p = 1 := by simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31806 p hg
    simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31808 (p : Pattern) (guard : d259579 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d259578 p = 1 := by simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31807 p hg
    simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30891 p hg
    simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31809 (p : Pattern) (guard : d259580 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259579 p = 1 := by simpa only [d259580, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31808 p hg
    simpa only [d259580, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259580, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30903 p hg
    simpa only [d259580, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31810 (p : Pattern) (guard : d259581 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258184 p = 1 := by simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31790 p hg
    simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259580 p = 1 := by simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31809 p hg
    simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31811 (p : Pattern) (guard : d259743 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d259743, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259581 p = 1 := by simpa only [d259743, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31810 p hg
    simpa only [d259743, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31812 (p : Pattern) (guard : d259582 p = 1) : d47797 p ≤ (-2 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259581 p = 1 := by simpa only [d259582, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31647 p hg
    simpa only [d259582, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259582, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d259582, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31813 (p : Pattern) (guard : d259744 p = 1) : d47798 p ≤ (-2 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259743 p = 1 := by simpa only [d259744, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31811 p hg
    simpa only [d259744, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259582 p = 1 := by simpa only [d259744, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31812 p hg
    simpa only [d259744, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31814 (p : Pattern) (guard : d259573 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 225 with
  | false =>
    have hg : d258806 p = 1 := by simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31069 p hg
    simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d259573, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31815 (p : Pattern) (guard : d259574 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259573 p = 1 := by simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31814 p hg
    simpa only [d259574, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31816 (p : Pattern) (guard : d259575 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 223 with
  | false =>
    have hg : d257871 p = 1 := by simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31521 p hg
    simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259574 p = 1 := by simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31815 p hg
    simpa only [d259575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31817 (p : Pattern) (guard : d259576 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d258695 p = 1 := by simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30916 p hg
    simpa only [d259576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31818 (p : Pattern) (guard : d259577 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 204 with
  | false =>
    have hg : d259575 p = 1 := by simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31816 p hg
    simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259576 p = 1 := by simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31817 p hg
    simpa only [d259577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31819 (p : Pattern) (guard : d259578 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 202 with
  | false =>
    have hg : d259577 p = 1 := by simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31818 p hg
    simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d259578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31820 (p : Pattern) (guard : d259579 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d259578 p = 1 := by simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31819 p hg
    simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30909 p hg
    simpa only [d259579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31821 (p : Pattern) (guard : d259580 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259579 p = 1 := by simpa only [d259580, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31820 p hg
    simpa only [d259580, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259580, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30921 p hg
    simpa only [d259580, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31822 (p : Pattern) (guard : d259581 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d258184 p = 1 := by simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31796 p hg
    simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259580 p = 1 := by simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31821 p hg
    simpa only [d259581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31823 (p : Pattern) (guard : d259582 p = 1) : d47682 p ≤ (-2 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259581 p = 1 := by simpa only [d259582, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31822 p hg
    simpa only [d259582, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259582, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259582, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31824 (p : Pattern) (guard : d259583 p = 1) : d47683 p ≤ (-2 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259582 p = 1 := by simpa only [d259583, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31823 p hg
    simpa only [d259583, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259583, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259583, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31825 (p : Pattern) (guard : d259745 p = 1) : d47799 p ≤ (-2 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259744 p = 1 := by simpa only [d259745, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31813 p hg
    simpa only [d259745, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259583 p = 1 := by simpa only [d259745, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31824 p hg
    simpa only [d259745, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31826 (p : Pattern) (guard : d259746 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259745 p = 1 := by simpa only [d259746, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31825 p hg
    simpa only [d259746, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259746, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d259746, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31827 (p : Pattern) (guard : d259747 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d258277 p = 1 := by simpa only [d259747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31801 p hg
    simpa only [d259747, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259746 p = 1 := by simpa only [d259747, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31826 p hg
    simpa only [d259747, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31828 (p : Pattern) (guard : d259587 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259580 p = 1 := by simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31809 p hg
    simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31829 (p : Pattern) (guard : d259749 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d259749, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259587 p = 1 := by simpa only [d259749, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31828 p hg
    simpa only [d259749, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31830 (p : Pattern) (guard : d259588 p = 1) : d47797 p ≤ (-2 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259587 p = 1 := by simpa only [d259588, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31653 p hg
    simpa only [d259588, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259588, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d259588, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31831 (p : Pattern) (guard : d259750 p = 1) : d47798 p ≤ (-2 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259749 p = 1 := by simpa only [d259750, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31829 p hg
    simpa only [d259750, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259588 p = 1 := by simpa only [d259750, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31830 p hg
    simpa only [d259750, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31832 (p : Pattern) (guard : d259587 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259580 p = 1 := by simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31821 p hg
    simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30923 p hg
    simpa only [d259587, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31833 (p : Pattern) (guard : d259588 p = 1) : d47682 p ≤ (-2 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259587 p = 1 := by simpa only [d259588, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31832 p hg
    simpa only [d259588, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259588, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259588, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31834 (p : Pattern) (guard : d259589 p = 1) : d47683 p ≤ (-2 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259588 p = 1 := by simpa only [d259589, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31833 p hg
    simpa only [d259589, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259589, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259589, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31835 (p : Pattern) (guard : d259751 p = 1) : d47799 p ≤ (-2 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259750 p = 1 := by simpa only [d259751, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31831 p hg
    simpa only [d259751, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259589 p = 1 := by simpa only [d259751, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31834 p hg
    simpa only [d259751, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31836 (p : Pattern) (guard : d259752 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259751 p = 1 := by simpa only [d259752, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31835 p hg
    simpa only [d259752, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259752, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d259752, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31837 (p : Pattern) (guard : d259753 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259746 p = 1 := by simpa only [d259753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31826 p hg
    simpa only [d259753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259752 p = 1 := by simpa only [d259753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31836 p hg
    simpa only [d259753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31838 (p : Pattern) (guard : d259754 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259747 p = 1 := by simpa only [d259754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31827 p hg
    simpa only [d259754, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259753 p = 1 := by simpa only [d259754, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31837 p hg
    simpa only [d259754, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31839 (p : Pattern) (guard : d259594 p = 1) : d47630 p ≤ (-2 : Int) + d47629 p := by
  cases selected : p 201 with
  | false =>
    have hg : d259578 p = 1 := by simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31807 p hg
    simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31538 p hg
    simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31840 (p : Pattern) (guard : d259595 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259594 p = 1 := by simpa only [d259595, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31839 p hg
    simpa only [d259595, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259595, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30903 p hg
    simpa only [d259595, d47652, d253301, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31841 (p : Pattern) (guard : d259596 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259595 p = 1 := by simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31840 p hg
    simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31842 (p : Pattern) (guard : d259764 p = 1) : d47652 p ≤ (-2 : Int) + d253301 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30890 p hg
    simpa only [d259764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259596 p = 1 := by simpa only [d259764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31841 p hg
    simpa only [d259764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31843 (p : Pattern) (guard : d259597 p = 1) : d47797 p ≤ (-2 : Int) + d253434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259596 p = 1 := by simpa only [d259597, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31662 p hg
    simpa only [d259597, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259597, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30852 p hg
    simpa only [d259597, d47797, d253434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31844 (p : Pattern) (guard : d259765 p = 1) : d47798 p ≤ (-2 : Int) + d253435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259764 p = 1 := by simpa only [d259765, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31842 p hg
    simpa only [d259765, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259597 p = 1 := by simpa only [d259765, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31843 p hg
    simpa only [d259765, d47798, d253435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31845 (p : Pattern) (guard : d259594 p = 1) : d47634 p ≤ (-2 : Int) + d47633 p := by
  cases selected : p 201 with
  | false =>
    have hg : d259578 p = 1 := by simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31819 p hg
    simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d27032 p = 1 := by simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31551 p hg
    simpa only [d259594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31846 (p : Pattern) (guard : d259595 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 182 with
  | false =>
    have hg : d259594 p = 1 := by simpa only [d259595, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31845 p hg
    simpa only [d259595, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259595, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30921 p hg
    simpa only [d259595, d47677, d253324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31847 (p : Pattern) (guard : d259596 p = 1) : d47677 p ≤ (-2 : Int) + d253324 p := by
  cases selected : p 180 with
  | false =>
    have hg : d259595 p = 1 := by simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31846 p hg
    simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30923 p hg
    simpa only [d259596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31848 (p : Pattern) (guard : d259597 p = 1) : d47682 p ≤ (-2 : Int) + d253329 p := by
  cases selected : p 163 with
  | false =>
    have hg : d259596 p = 1 := by simpa only [d259597, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31847 p hg
    simpa only [d259597, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259597, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259597, d47682, d253329, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31849 (p : Pattern) (guard : d259598 p = 1) : d47683 p ≤ (-2 : Int) + d253330 p := by
  cases selected : p 162 with
  | false =>
    have hg : d259597 p = 1 := by simpa only [d259598, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31848 p hg
    simpa only [d259598, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259598, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8018 p hg
    simpa only [d259598, d47683, d253330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31850 (p : Pattern) (guard : d259766 p = 1) : d47799 p ≤ (-2 : Int) + d253436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d259765 p = 1 := by simpa only [d259766, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31844 p hg
    simpa only [d259766, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259598 p = 1 := by simpa only [d259766, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31849 p hg
    simpa only [d259766, d47799, d253436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31851 (p : Pattern) (guard : d259767 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 160 with
  | false =>
    have hg : d259766 p = 1 := by simpa only [d259767, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31850 p hg
    simpa only [d259767, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259767, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30928 p hg
    simpa only [d259767, d47803, d253440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31852 (p : Pattern) (guard : d259768 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259746 p = 1 := by simpa only [d259768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31826 p hg
    simpa only [d259768, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259767 p = 1 := by simpa only [d259768, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31851 p hg
    simpa only [d259768, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31853 (p : Pattern) (guard : d259758 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259752 p = 1 := by simpa only [d259758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31836 p hg
    simpa only [d259758, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259758, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30930 p hg
    simpa only [d259758, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31854 (p : Pattern) (guard : d259769 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259768 p = 1 := by simpa only [d259769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31852 p hg
    simpa only [d259769, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259758 p = 1 := by simpa only [d259769, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31853 p hg
    simpa only [d259769, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31855 (p : Pattern) (guard : d259770 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259754 p = 1 := by simpa only [d259770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31838 p hg
    simpa only [d259770, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259769 p = 1 := by simpa only [d259770, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31854 p hg
    simpa only [d259770, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31856 (p : Pattern) (guard : d259771 p = 1) : d47804 p ≤ (-2 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259771, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30889 p hg
    simpa only [d259771, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259770 p = 1 := by simpa only [d259771, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31855 p hg
    simpa only [d259771, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31857 (p : Pattern) (guard : d259772 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259772, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30888 p hg
    simpa only [d259772, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259771 p = 1 := by simpa only [d259772, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31856 p hg
    simpa only [d259772, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31858 (p : Pattern) (guard : d259773 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 159 with
  | false =>
    have hg : d259767 p = 1 := by simpa only [d259773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31851 p hg
    simpa only [d259773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30930 p hg
    simpa only [d259773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31859 (p : Pattern) (guard : d259774 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 158 with
  | false =>
    have hg : d259773 p = 1 := by simpa only [d259774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31858 p hg
    simpa only [d259774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30930 p hg
    simpa only [d259774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31860 (p : Pattern) (guard : d259775 p = 1) : d47803 p ≤ (-2 : Int) + d253440 p := by
  cases selected : p 157 with
  | false =>
    have hg : d259769 p = 1 := by simpa only [d259775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31854 p hg
    simpa only [d259775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259774 p = 1 := by simpa only [d259775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31859 p hg
    simpa only [d259775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31861 (p : Pattern) (guard : d259776 p = 1) : d47804 p ≤ (-2 : Int) + d253441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259776, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30889 p hg
    simpa only [d259776, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259775 p = 1 := by simpa only [d259776, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31860 p hg
    simpa only [d259776, d47804, d253441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31862 (p : Pattern) (guard : d259777 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259777, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30888 p hg
    simpa only [d259777, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259776 p = 1 := by simpa only [d259777, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31861 p hg
    simpa only [d259777, d47805, d253442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31863 (p : Pattern) (guard : d259778 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259772 p = 1 := by simpa only [d259778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31857 p hg
    simpa only [d259778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259777 p = 1 := by simpa only [d259778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31862 p hg
    simpa only [d259778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31864 (p : Pattern) (guard : d259783 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 136 with
  | false =>
    have hg : d259777 p = 1 := by simpa only [d259783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31862 p hg
    simpa only [d259783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d259783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31865 (p : Pattern) (guard : d259784 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259778 p = 1 := by simpa only [d259784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31863 p hg
    simpa only [d259784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259783 p = 1 := by simpa only [d259784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31864 p hg
    simpa only [d259784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31866 (p : Pattern) (guard : d259785 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259784 p = 1 := by simpa only [d259785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31865 p hg
    simpa only [d259785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d259785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31867 (p : Pattern) (guard : d259786 p = 1) : d47807 p ≤ (-2 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259785 p = 1 := by simpa only [d259786, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31866 p hg
    simpa only [d259786, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259786, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30940 p hg
    simpa only [d259786, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31868 (p : Pattern) (guard : d259787 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259787, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d259787, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259786 p = 1 := by simpa only [d259787, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31867 p hg
    simpa only [d259787, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31869 (p : Pattern) (guard : d259792 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 135 with
  | false =>
    have hg : d259783 p = 1 := by simpa only [d259792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31864 p hg
    simpa only [d259792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d259792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31870 (p : Pattern) (guard : d259793 p = 1) : d47805 p ≤ (-2 : Int) + d253442 p := by
  cases selected : p 119 with
  | false =>
    have hg : d259792 p = 1 := by simpa only [d259793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31869 p hg
    simpa only [d259793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30936 p hg
    simpa only [d259793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31871 (p : Pattern) (guard : d259794 p = 1) : d47807 p ≤ (-2 : Int) + d253444 p := by
  cases selected : p 116 with
  | false =>
    have hg : d259793 p = 1 := by simpa only [d259794, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31870 p hg
    simpa only [d259794, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259794, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30940 p hg
    simpa only [d259794, d47807, d253444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31872 (p : Pattern) (guard : d259795 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d259795, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30769 p hg
    simpa only [d259795, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259794 p = 1 := by simpa only [d259795, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31871 p hg
    simpa only [d259795, d47808, d253445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31873 (p : Pattern) (guard : d259796 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259787 p = 1 := by simpa only [d259796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31868 p hg
    simpa only [d259796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259795 p = 1 := by simpa only [d259796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31872 p hg
    simpa only [d259796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31874 (p : Pattern) (guard : d259797 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259796 p = 1 := by simpa only [d259797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31873 p hg
    simpa only [d259797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31875 (p : Pattern) (guard : d259798 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259797 p = 1 := by simpa only [d259798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31874 p hg
    simpa only [d259798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31876 (p : Pattern) (guard : d259799 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259798 p = 1 := by simpa only [d259799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31875 p hg
    simpa only [d259799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31877 (p : Pattern) (guard : d259813 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 113 with
  | false =>
    have hg : d259795 p = 1 := by simpa only [d259813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31872 p hg
    simpa only [d259813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31878 (p : Pattern) (guard : d259814 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 96 with
  | false =>
    have hg : d259813 p = 1 := by simpa only [d259814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31877 p hg
    simpa only [d259814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31879 (p : Pattern) (guard : d259815 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 95 with
  | false =>
    have hg : d259814 p = 1 := by simpa only [d259815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31878 p hg
    simpa only [d259815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31880 (p : Pattern) (guard : d259816 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 93 with
  | false =>
    have hg : d259815 p = 1 := by simpa only [d259816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31879 p hg
    simpa only [d259816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d259816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d259816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31881 (p : Pattern) (guard : d260199 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 91 with
  | false =>
    have hg : d259799 p = 1 := by simpa only [d260199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31876 p hg
    simpa only [d260199, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d259816 p = 1 := by simpa only [d260199, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31880 p hg
    simpa only [d260199, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31882 (p : Pattern) (guard : d260200 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d260200, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260199 p = 1 := by simpa only [d260200, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31881 p hg
    simpa only [d260200, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31883 (p : Pattern) (guard : d260201 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 89 with
  | false =>
    have hg : d260200 p = 1 := by simpa only [d260201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31882 p hg
    simpa only [d260201, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260201, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d260201, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31884 (p : Pattern) (guard : d260202 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d260202, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260201 p = 1 := by simpa only [d260202, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31883 p hg
    simpa only [d260202, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31885 (p : Pattern) (guard : d260203 p = 1) : d47808 p ≤ (-2 : Int) + d253445 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30887 p hg
    simpa only [d260203, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260202 p = 1 := by simpa only [d260203, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31884 p hg
    simpa only [d260203, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31886 (p : Pattern) (guard : d260204 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260204, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30768 p hg
    simpa only [d260204, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260203 p = 1 := by simpa only [d260204, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31885 p hg
    simpa only [d260204, d47809, d253446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31887 (p : Pattern) (guard : d260205 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260205, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260204 p = 1 := by simpa only [d260205, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31886 p hg
    simpa only [d260205, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31888 (p : Pattern) (guard : d260206 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 69 with
  | false =>
    have hg : d260205 p = 1 := by simpa only [d260206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31887 p hg
    simpa only [d260206, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260206, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260206, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31889 (p : Pattern) (guard : d260207 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 51 with
  | false =>
    have hg : d260206 p = 1 := by simpa only [d260207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31888 p hg
    simpa only [d260207, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260207, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260207, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31890 (p : Pattern) (guard : d260208 p = 1) : d47809 p ≤ (-2 : Int) + d253446 p := by
  cases selected : p 50 with
  | false =>
    have hg : d260207 p = 1 := by simpa only [d260208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31889 p hg
    simpa only [d260208, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260208, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30886 p hg
    simpa only [d260208, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31891 (p : Pattern) (guard : d260209 p = 1) : d47865 p ≤ (-2 : Int) + d253502 p := by
  cases selected : p 49 with
  | false =>
    have hg : d260208 p = 1 := by simpa only [d260209, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31890 p hg
    simpa only [d260209, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260209, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30957 p hg
    simpa only [d260209, d47865, d253502, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31892 (p : Pattern) (guard : d260210 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 48 with
  | false =>
    have hg : d260198 p = 1 := by simpa only [d260210, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31788 p hg
    simpa only [d260210, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260209 p = 1 := by simpa only [d260210, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31891 p hg
    simpa only [d260210, d47866, d253503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31893 (p : Pattern) (guard : d260211 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260211, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260210 p = 1 := by simpa only [d260211, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31892 p hg
    simpa only [d260211, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31894 (p : Pattern) (guard : d260212 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260212, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260211 p = 1 := by simpa only [d260212, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31893 p hg
    simpa only [d260212, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31895 (p : Pattern) (guard : d260213 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260213, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260212 p = 1 := by simpa only [d260213, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31894 p hg
    simpa only [d260213, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31896 (p : Pattern) (guard : d260214 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260214, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260213 p = 1 := by simpa only [d260214, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31895 p hg
    simpa only [d260214, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31897 (p : Pattern) (guard : d260215 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260215, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260214 p = 1 := by simpa only [d260215, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31896 p hg
    simpa only [d260215, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31898 (p : Pattern) (guard : d260216 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260216, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260215 p = 1 := by simpa only [d260216, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31897 p hg
    simpa only [d260216, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31899 (p : Pattern) (guard : d260217 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260217, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260216 p = 1 := by simpa only [d260217, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31898 p hg
    simpa only [d260217, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31900 (p : Pattern) (guard : d260218 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260218, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260217 p = 1 := by simpa only [d260218, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31899 p hg
    simpa only [d260218, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31901 (p : Pattern) (guard : d260219 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260219, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260218 p = 1 := by simpa only [d260219, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31900 p hg
    simpa only [d260219, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31902 (p : Pattern) (guard : d260220 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d260220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260220, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260219 p = 1 := by simpa only [d260220, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31901 p hg
    simpa only [d260220, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31903 (p : Pattern) (guard : d260221 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 10250 with
  | false =>
    have hg : d260190 p = 1 := by simpa only [d260221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31631 p hg
    simpa only [d260221, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d260220 p = 1 := by simpa only [d260221, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31902 p hg
    simpa only [d260221, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31904 (p : Pattern) (guard : d260222 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 260 with
  | false =>
    have hg : d260221 p = 1 := by simpa only [d260222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31903 p hg
    simpa only [d260222, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260222, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260222, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31905 (p : Pattern) (guard : d260223 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 259 with
  | false =>
    have hg : d260222 p = 1 := by simpa only [d260223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31904 p hg
    simpa only [d260223, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260223, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260223, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31906 (p : Pattern) (guard : d260224 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 258 with
  | false =>
    have hg : d260223 p = 1 := by simpa only [d260224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31905 p hg
    simpa only [d260224, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260224, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260224, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31907 (p : Pattern) (guard : d260225 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 257 with
  | false =>
    have hg : d260224 p = 1 := by simpa only [d260225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31906 p hg
    simpa only [d260225, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260225, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260225, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31908 (p : Pattern) (guard : d260226 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 256 with
  | false =>
    have hg : d260225 p = 1 := by simpa only [d260226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31907 p hg
    simpa only [d260226, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260226, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260226, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31909 (p : Pattern) (guard : d260227 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 255 with
  | false =>
    have hg : d260226 p = 1 := by simpa only [d260227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31908 p hg
    simpa only [d260227, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260227, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260227, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31910 (p : Pattern) (guard : d260228 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 254 with
  | false =>
    have hg : d260227 p = 1 := by simpa only [d260228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31909 p hg
    simpa only [d260228, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260228, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260228, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31911 (p : Pattern) (guard : d260229 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 253 with
  | false =>
    have hg : d260228 p = 1 := by simpa only [d260229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31910 p hg
    simpa only [d260229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31912 (p : Pattern) (guard : d260230 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 252 with
  | false =>
    have hg : d260229 p = 1 := by simpa only [d260230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31911 p hg
    simpa only [d260230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31913 (p : Pattern) (guard : d260231 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 251 with
  | false =>
    have hg : d260230 p = 1 := by simpa only [d260231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31912 p hg
    simpa only [d260231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31914 (p : Pattern) (guard : d260232 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 250 with
  | false =>
    have hg : d260231 p = 1 := by simpa only [d260232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31913 p hg
    simpa only [d260232, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260232, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260232, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31915 (p : Pattern) (guard : d260233 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 249 with
  | false =>
    have hg : d260232 p = 1 := by simpa only [d260233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31914 p hg
    simpa only [d260233, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260233, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260233, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31916 (p : Pattern) (guard : d260234 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 245 with
  | false =>
    have hg : d260233 p = 1 := by simpa only [d260234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31915 p hg
    simpa only [d260234, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260234, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260234, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31917 (p : Pattern) (guard : d260235 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 200 with
  | false =>
    have hg : d260234 p = 1 := by simpa only [d260235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31916 p hg
    simpa only [d260235, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260235, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260235, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31918 (p : Pattern) (guard : d260236 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 199 with
  | false =>
    have hg : d260235 p = 1 := by simpa only [d260236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31917 p hg
    simpa only [d260236, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260236, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260236, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31919 (p : Pattern) (guard : d260237 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 186 with
  | false =>
    have hg : d260236 p = 1 := by simpa only [d260237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31918 p hg
    simpa only [d260237, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260237, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260237, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31920 (p : Pattern) (guard : d260238 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 185 with
  | false =>
    have hg : d260237 p = 1 := by simpa only [d260238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31919 p hg
    simpa only [d260238, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260238, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260238, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31921 (p : Pattern) (guard : d260239 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 184 with
  | false =>
    have hg : d260238 p = 1 := by simpa only [d260239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31920 p hg
    simpa only [d260239, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260239, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260239, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31922 (p : Pattern) (guard : d260240 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 181 with
  | false =>
    have hg : d260239 p = 1 := by simpa only [d260240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31921 p hg
    simpa only [d260240, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260240, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260240, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31923 (p : Pattern) (guard : d260241 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 177 with
  | false =>
    have hg : d260240 p = 1 := by simpa only [d260241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31922 p hg
    simpa only [d260241, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260241, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260241, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31924 (p : Pattern) (guard : d260242 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 164 with
  | false =>
    have hg : d260241 p = 1 := by simpa only [d260242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31923 p hg
    simpa only [d260242, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260242, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260242, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31925 (p : Pattern) (guard : d260243 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 156 with
  | false =>
    have hg : d260242 p = 1 := by simpa only [d260243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31924 p hg
    simpa only [d260243, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260243, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260243, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31926 (p : Pattern) (guard : d260244 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 155 with
  | false =>
    have hg : d260243 p = 1 := by simpa only [d260244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31925 p hg
    simpa only [d260244, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260244, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260244, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31927 (p : Pattern) (guard : d260245 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 134 with
  | false =>
    have hg : d260244 p = 1 := by simpa only [d260245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31926 p hg
    simpa only [d260245, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260245, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260245, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31928 (p : Pattern) (guard : d260246 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 133 with
  | false =>
    have hg : d260245 p = 1 := by simpa only [d260246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31927 p hg
    simpa only [d260246, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260246, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260246, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31929 (p : Pattern) (guard : d260247 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 120 with
  | false =>
    have hg : d260246 p = 1 := by simpa only [d260247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31928 p hg
    simpa only [d260247, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260247, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260247, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31930 (p : Pattern) (guard : d260248 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 118 with
  | false =>
    have hg : d260247 p = 1 := by simpa only [d260248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31929 p hg
    simpa only [d260248, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260248, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260248, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31931 (p : Pattern) (guard : d260249 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 114 with
  | false =>
    have hg : d260248 p = 1 := by simpa only [d260249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31930 p hg
    simpa only [d260249, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260249, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260249, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31932 (p : Pattern) (guard : d260250 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 111 with
  | false =>
    have hg : d260249 p = 1 := by simpa only [d260250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31931 p hg
    simpa only [d260250, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260250, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260250, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31933 (p : Pattern) (guard : d260251 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 98 with
  | false =>
    have hg : d260250 p = 1 := by simpa only [d260251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31932 p hg
    simpa only [d260251, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260251, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260251, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31934 (p : Pattern) (guard : d260252 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 97 with
  | false =>
    have hg : d260251 p = 1 := by simpa only [d260252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31933 p hg
    simpa only [d260252, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260252, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260252, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31935 (p : Pattern) (guard : d260253 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 94 with
  | false =>
    have hg : d260252 p = 1 := by simpa only [d260253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31934 p hg
    simpa only [d260253, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260253, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260253, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31936 (p : Pattern) (guard : d260254 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 76 with
  | false =>
    have hg : d260253 p = 1 := by simpa only [d260254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31935 p hg
    simpa only [d260254, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260254, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260254, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31937 (p : Pattern) (guard : d260255 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 67 with
  | false =>
    have hg : d260254 p = 1 := by simpa only [d260255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31936 p hg
    simpa only [d260255, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260255, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260255, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31938 (p : Pattern) (guard : d260256 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 52 with
  | false =>
    have hg : d260255 p = 1 := by simpa only [d260256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31937 p hg
    simpa only [d260256, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260256, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260256, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31939 (p : Pattern) (guard : d260257 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 47 with
  | false =>
    have hg : d260256 p = 1 := by simpa only [d260257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31938 p hg
    simpa only [d260257, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260257, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260257, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31940 (p : Pattern) (guard : d260258 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 46 with
  | false =>
    have hg : d260257 p = 1 := by simpa only [d260258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31939 p hg
    simpa only [d260258, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260258, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260258, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31941 (p : Pattern) (guard : d260259 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 45 with
  | false =>
    have hg : d260258 p = 1 := by simpa only [d260259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31940 p hg
    simpa only [d260259, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260259, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260259, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31942 (p : Pattern) (guard : d260260 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 30 with
  | false =>
    have hg : d260259 p = 1 := by simpa only [d260260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31941 p hg
    simpa only [d260260, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260260, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260260, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31943 (p : Pattern) (guard : d260261 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 29 with
  | false =>
    have hg : d260260 p = 1 := by simpa only [d260261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31942 p hg
    simpa only [d260261, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260261, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260261, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31944 (p : Pattern) (guard : d260262 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 28 with
  | false =>
    have hg : d260261 p = 1 := by simpa only [d260262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31943 p hg
    simpa only [d260262, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260262, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260262, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31945 (p : Pattern) (guard : d260263 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 27 with
  | false =>
    have hg : d260262 p = 1 := by simpa only [d260263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31944 p hg
    simpa only [d260263, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260263, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260263, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31946 (p : Pattern) (guard : d260264 p = 1) : d47866 p ≤ (-2 : Int) + d253503 p := by
  cases selected : p 25 with
  | false =>
    have hg : d260263 p = 1 := by simpa only [d260264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31945 p hg
    simpa only [d260264, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d260264, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare30767 p hg
    simpa only [d260264, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31947 (p : Pattern) (guard : d261795 p = 1) : d47866 p ≤ (1 : Int) + d47866 p := by
  omega
theorem compare31948 (p : Pattern) (guard : d261982 p = 1) : d47866 p ≤ (0 : Int) + d47866 p := by
  omega
theorem compare31949 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d50493 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31950 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d50493 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31951 (p : Pattern) (guard : d0 p = 1) : d49782 p ≤ (-1 : Int) + d49280 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31952 (p : Pattern) (guard : d0 p = 1) : d49782 p ≤ (-2 : Int) + d49280 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31953 (p : Pattern) (guard : d0 p = 1) : d49782 p ≤ (1 : Int) + d267843 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31954 (p : Pattern) (guard : d0 p = 1) : d49782 p ≤ (0 : Int) + d267843 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31955 (p : Pattern) (guard : d0 p = 1) : d49782 p ≤ (-1 : Int) + d50823 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31956 (p : Pattern) (guard : d0 p = 1) : d49782 p ≤ (-2 : Int) + d50823 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31957 (p : Pattern) (guard : d0 p = 1) : d49782 p ≤ (-1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31958 (p : Pattern) (guard : d0 p = 1) : d49782 p ≤ (-2 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31959 (p : Pattern) (guard : d0 p = 1) : d49782 p ≤ (-1 : Int) + d50493 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31960 (p : Pattern) (guard : d0 p = 1) : d49782 p ≤ (-2 : Int) + d50493 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31961 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-1 : Int) + d51138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31962 (p : Pattern) (guard : d0 p = 1) : d47866 p ≤ (-2 : Int) + d51138 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31963 (p : Pattern) (guard : d0 p = 1) : d50101 p ≤ (-1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31964 (p : Pattern) (guard : d0 p = 1) : d50101 p ≤ (-2 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31965 (p : Pattern) (guard : d0 p = 1) : d50101 p ≤ (1 : Int) + d47866 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31966 (p : Pattern) (guard : d0 p = 1) : d49916 p ≤ (1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31967 (p : Pattern) (guard : d0 p = 1) : d49895 p ≤ (1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31968 (p : Pattern) (guard : d0 p = 1) : d49915 p ≤ (1 : Int) + d47700 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31969 (p : Pattern) (guard : d0 p = 1) : d49910 p ≤ (1 : Int) + d47697 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31970 (p : Pattern) (guard : d0 p = 1) : d49912 p ≤ (1 : Int) + d47676 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31971 (p : Pattern) (guard : d0 p = 1) : d49861 p ≤ (1 : Int) + d47681 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31972 (p : Pattern) (guard : d0 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31973 (p : Pattern) (guard : d0 p = 1) : d49863 p ≤ (1 : Int) + d47655 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31974 (p : Pattern) (guard : d0 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31975 (p : Pattern) (guard : d17 p = 1) : d47617 p ≤ (1 : Int) + d47617 p := by
  omega
theorem compare31976 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (1 : Int) + d47617 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31977 (p : Pattern) (guard : d18 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 224 with
  | false =>
    have hg : d17 p = 1 := by simpa only [d18, d49795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31975 p hg
    simpa only [d18, d49795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18, d49795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31976 p hg
    simpa only [d18, d49795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31978 (p : Pattern) (guard : d19 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 223 with
  | false =>
    have hg : d18 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31977 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d19, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31979 (p : Pattern) (guard : d20 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 204 with
  | false =>
    have hg : d19 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31978 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31980 (p : Pattern) (guard : d29090 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d20 p = 1 := by simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31979 p hg
    simpa only [d29090, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31981 (p : Pattern) (guard : d294503 p = 1) : d49795 p ≤ (1 : Int) + d47617 p := by
  cases selected : p 201 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31974 p hg
    simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d29090 p = 1 := by simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31980 p hg
    simpa only [d294503, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31982 (p : Pattern) (guard : d0 p = 1) : d49796 p ≤ (1 : Int) + d47618 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31983 (p : Pattern) (guard : d294504 p = 1) : d49797 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 182 with
  | false =>
    have hg : d294503 p = 1 := by simpa only [d294504, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31981 p hg
    simpa only [d294504, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294504, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31982 p hg
    simpa only [d294504, d49797, d47619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31984 (p : Pattern) (guard : d0 p = 1) : d49797 p ≤ (1 : Int) + d47619 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31985 (p : Pattern) (guard : d294505 p = 1) : d49797 p ≤ (1 : Int) + d47619 p := by
  cases selected : p 180 with
  | false =>
    have hg : d294504 p = 1 := by simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31983 p hg
    simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31984 p hg
    simpa only [d294505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31986 (p : Pattern) (guard : d0 p = 1) : d49837 p ≤ (1 : Int) + d47659 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31987 (p : Pattern) (guard : d294506 p = 1) : d49838 p ≤ (1 : Int) + d47660 p := by
  cases selected : p 163 with
  | false =>
    have hg : d294505 p = 1 := by simpa only [d294506, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31985 p hg
    simpa only [d294506, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294506, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31986 p hg
    simpa only [d294506, d49838, d47660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31988 (p : Pattern) (guard : d0 p = 1) : d49840 p ≤ (1 : Int) + d47662 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31989 (p : Pattern) (guard : d294507 p = 1) : d49841 p ≤ (1 : Int) + d47663 p := by
  cases selected : p 162 with
  | false =>
    have hg : d294506 p = 1 := by simpa only [d294507, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31987 p hg
    simpa only [d294507, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294507, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31988 p hg
    simpa only [d294507, d49841, d47663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31990 (p : Pattern) (guard : d294508 p = 1) : d49864 p ≤ (1 : Int) + d47664 p := by
  cases selected : p 161 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294508, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31973 p hg
    simpa only [d294508, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294507 p = 1 := by simpa only [d294508, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31989 p hg
    simpa only [d294508, d49864, d47664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31991 (p : Pattern) (guard : d0 p = 1) : d49867 p ≤ (1 : Int) + d47684 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31992 (p : Pattern) (guard : d294509 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 160 with
  | false =>
    have hg : d294508 p = 1 := by simpa only [d294509, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31990 p hg
    simpa only [d294509, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294509, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31991 p hg
    simpa only [d294509, d49868, d47685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31993 (p : Pattern) (guard : d294510 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d294510, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294509 p = 1 := by simpa only [d294510, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31992 p hg
    simpa only [d294510, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31994 (p : Pattern) (guard : d294511 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 158 with
  | false =>
    have hg : d294510 p = 1 := by simpa only [d294511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31993 p hg
    simpa only [d294511, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294511, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d294511, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31995 (p : Pattern) (guard : d294512 p = 1) : d49868 p ≤ (1 : Int) + d47685 p := by
  cases selected : p 157 with
  | false =>
    have hg : d294511 p = 1 := by simpa only [d294512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31994 p hg
    simpa only [d294512, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294512, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31972 p hg
    simpa only [d294512, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31996 (p : Pattern) (guard : d294513 p = 1) : d49869 p ≤ (1 : Int) + d47686 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294513, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31971 p hg
    simpa only [d294513, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294512 p = 1 := by simpa only [d294513, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31995 p hg
    simpa only [d294513, d49869, d47686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31997 (p : Pattern) (guard : d294514 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d294514, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31970 p hg
    simpa only [d294514, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d294513 p = 1 := by simpa only [d294514, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31996 p hg
    simpa only [d294514, d49913, d47687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare31998 (p : Pattern) (guard : d0 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare31999 (p : Pattern) (guard : d294515 p = 1) : d49913 p ≤ (1 : Int) + d47687 p := by
  cases selected : p 136 with
  | false =>
    have hg : d294514 p = 1 := by simpa only [d294515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31997 p hg
    simpa only [d294515, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d294515, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare31998 p hg
    simpa only [d294515, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
