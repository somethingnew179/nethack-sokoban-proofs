import NetHack.Soko22Hazard87.Compare002
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Soko22Hazard87
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare750 (p : Pattern) (guard : d1575 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare721 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare751 (p : Pattern) (guard : d1576 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1575 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare750 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare524 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare752 (p : Pattern) (guard : d1577 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare751 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare727 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare753 (p : Pattern) (guard : d1578 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1565 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare727 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare754 (p : Pattern) (guard : d1579 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1577 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare752 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare753 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare755 (p : Pattern) (guard : d1580 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1579 p = 1 := by simpa only [d1580, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare754 p hg
    simpa only [d1580, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1580, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d1580, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare756 (p : Pattern) (guard : d1581 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare730 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1580 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare755 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare757 (p : Pattern) (guard : d1868 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1868, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d1868, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1581 p = 1 := by simpa only [d1868, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare756 p hg
    simpa only [d1868, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare758 (p : Pattern) (guard : d1575 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1559 p = 1 := by simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare733 p hg
    simpa only [d1575, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare759 (p : Pattern) (guard : d1576 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1575 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare758 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1115 p = 1 := by simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare531 p hg
    simpa only [d1576, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare760 (p : Pattern) (guard : d1577 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare759 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1565 p = 1 := by simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare739 p hg
    simpa only [d1577, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare761 (p : Pattern) (guard : d1578 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1565 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare739 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1578, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare762 (p : Pattern) (guard : d1579 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1577 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare760 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1578 p = 1 := by simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare761 p hg
    simpa only [d1579, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare763 (p : Pattern) (guard : d1580 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1579 p = 1 := by simpa only [d1580, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare762 p hg
    simpa only [d1580, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1580, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d1580, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare764 (p : Pattern) (guard : d1581 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1568 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare742 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1580 p = 1 := by simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare763 p hg
    simpa only [d1581, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare765 (p : Pattern) (guard : d1582 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1581 p = 1 := by simpa only [d1582, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare764 p hg
    simpa only [d1582, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1582, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d1582, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare766 (p : Pattern) (guard : d1869 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1868 p = 1 := by simpa only [d1869, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare757 p hg
    simpa only [d1869, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1582 p = 1 := by simpa only [d1869, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare765 p hg
    simpa only [d1869, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare767 (p : Pattern) (guard : d18188 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1869 p = 1 := by simpa only [d18188, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare766 p hg
    simpa only [d18188, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18188, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d18188, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare768 (p : Pattern) (guard : d18189 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d18188 p = 1 := by simpa only [d18189, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare767 p hg
    simpa only [d18189, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18189, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d18189, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare769 (p : Pattern) (guard : d60778 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d18156 p = 1 := by simpa only [d60778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare747 p hg
    simpa only [d60778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18189 p = 1 := by simpa only [d60778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare768 p hg
    simpa only [d60778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare770 (p : Pattern) (guard : d60779 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60776 p = 1 := by simpa only [d60779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare748 p hg
    simpa only [d60779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60778 p = 1 := by simpa only [d60779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare769 p hg
    simpa only [d60779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare771 (p : Pattern) (guard : d60780 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60777 p = 1 := by simpa only [d60780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare749 p hg
    simpa only [d60780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60779 p = 1 := by simpa only [d60780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare770 p hg
    simpa only [d60780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare772 (p : Pattern) (guard : d60781 p = 1) : d47804 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60781, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d60781, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60780 p = 1 := by simpa only [d60781, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare771 p hg
    simpa only [d60781, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare773 (p : Pattern) (guard : d60782 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60782, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d60782, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60781 p = 1 := by simpa only [d60782, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare772 p hg
    simpa only [d60782, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare774 (p : Pattern) (guard : d18190 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d18189 p = 1 := by simpa only [d18190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare768 p hg
    simpa only [d18190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d18190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare775 (p : Pattern) (guard : d60783 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60778 p = 1 := by simpa only [d60783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare769 p hg
    simpa only [d60783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18190 p = 1 := by simpa only [d60783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare774 p hg
    simpa only [d60783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare776 (p : Pattern) (guard : d60784 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60779 p = 1 := by simpa only [d60784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare770 p hg
    simpa only [d60784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60783 p = 1 := by simpa only [d60784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare775 p hg
    simpa only [d60784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare777 (p : Pattern) (guard : d60785 p = 1) : d47804 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60785, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d60785, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60784 p = 1 := by simpa only [d60785, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare776 p hg
    simpa only [d60785, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare778 (p : Pattern) (guard : d60786 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60786, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d60786, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60785 p = 1 := by simpa only [d60786, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare777 p hg
    simpa only [d60786, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare779 (p : Pattern) (guard : d60787 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60782 p = 1 := by simpa only [d60787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare773 p hg
    simpa only [d60787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60786 p = 1 := by simpa only [d60787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d60787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare780 (p : Pattern) (guard : d1593 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare751 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare781 (p : Pattern) (guard : d1594 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1593 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare780 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare782 (p : Pattern) (guard : d1595 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1594 p = 1 := by simpa only [d1595, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare781 p hg
    simpa only [d1595, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1595, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d1595, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare783 (p : Pattern) (guard : d1596 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1595 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare782 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare784 (p : Pattern) (guard : d1883 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1883, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d1883, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1596 p = 1 := by simpa only [d1883, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare783 p hg
    simpa only [d1883, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare785 (p : Pattern) (guard : d1593 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d1576 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare759 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1593, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare786 (p : Pattern) (guard : d1594 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d1593 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare785 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1594, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare787 (p : Pattern) (guard : d1595 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d1594 p = 1 := by simpa only [d1595, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare786 p hg
    simpa only [d1595, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1595, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d1595, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare788 (p : Pattern) (guard : d1596 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d1595 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare787 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare55 p hg
    simpa only [d1596, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare789 (p : Pattern) (guard : d1597 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d1596 p = 1 := by simpa only [d1597, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare788 p hg
    simpa only [d1597, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1597, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d1597, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare790 (p : Pattern) (guard : d1884 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d1883 p = 1 := by simpa only [d1884, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare784 p hg
    simpa only [d1884, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1597 p = 1 := by simpa only [d1884, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare789 p hg
    simpa only [d1884, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare791 (p : Pattern) (guard : d60788 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1884 p = 1 := by simpa only [d60788, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare790 p hg
    simpa only [d60788, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60788, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d60788, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare792 (p : Pattern) (guard : d60789 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d60788 p = 1 := by simpa only [d60789, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare791 p hg
    simpa only [d60789, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60789, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d60789, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare793 (p : Pattern) (guard : d60790 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d60789 p = 1 := by simpa only [d60790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare792 p hg
    simpa only [d60790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare64 p hg
    simpa only [d60790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare794 (p : Pattern) (guard : d60791 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d18190 p = 1 := by simpa only [d60791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare774 p hg
    simpa only [d60791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60790 p = 1 := by simpa only [d60791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare793 p hg
    simpa only [d60791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare795 (p : Pattern) (guard : d60792 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 157 with
  | false =>
    have hg : d60783 p = 1 := by simpa only [d60792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare775 p hg
    simpa only [d60792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60791 p = 1 := by simpa only [d60792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare794 p hg
    simpa only [d60792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare796 (p : Pattern) (guard : d60793 p = 1) : d47804 p ≤ (0 : Int) + d47756 p := by
  cases selected : p 141 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60793, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare24 p hg
    simpa only [d60793, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60792 p = 1 := by simpa only [d60793, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare795 p hg
    simpa only [d60793, d47804, d47756, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare797 (p : Pattern) (guard : d60794 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 138 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60794, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23 p hg
    simpa only [d60794, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60793 p = 1 := by simpa only [d60794, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare796 p hg
    simpa only [d60794, d47805, d47757, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare798 (p : Pattern) (guard : d60795 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60786 p = 1 := by simpa only [d60795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare778 p hg
    simpa only [d60795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60794 p = 1 := by simpa only [d60795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare797 p hg
    simpa only [d60795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare799 (p : Pattern) (guard : d60796 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60787 p = 1 := by simpa only [d60796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare779 p hg
    simpa only [d60796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60795 p = 1 := by simpa only [d60796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare798 p hg
    simpa only [d60796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare800 (p : Pattern) (guard : d60797 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60796 p = 1 := by simpa only [d60797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare799 p hg
    simpa only [d60797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare801 (p : Pattern) (guard : d60798 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60797 p = 1 := by simpa only [d60798, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare800 p hg
    simpa only [d60798, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60798, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d60798, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare802 (p : Pattern) (guard : d60799 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60799, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d60799, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60798 p = 1 := by simpa only [d60799, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare801 p hg
    simpa only [d60799, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare803 (p : Pattern) (guard : d60800 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 136 with
  | false =>
    have hg : d60794 p = 1 := by simpa only [d60800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare797 p hg
    simpa only [d60800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare804 (p : Pattern) (guard : d60801 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60795 p = 1 := by simpa only [d60801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare798 p hg
    simpa only [d60801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60800 p = 1 := by simpa only [d60801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare803 p hg
    simpa only [d60801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare805 (p : Pattern) (guard : d60802 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60801 p = 1 := by simpa only [d60802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare804 p hg
    simpa only [d60802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare806 (p : Pattern) (guard : d60803 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60802 p = 1 := by simpa only [d60803, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare805 p hg
    simpa only [d60803, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60803, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d60803, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare807 (p : Pattern) (guard : d60804 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60804, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d60804, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60803 p = 1 := by simpa only [d60804, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare806 p hg
    simpa only [d60804, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare808 (p : Pattern) (guard : d60805 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60799 p = 1 := by simpa only [d60805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare802 p hg
    simpa only [d60805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60804 p = 1 := by simpa only [d60805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare807 p hg
    simpa only [d60805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare809 (p : Pattern) (guard : d60806 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60805 p = 1 := by simpa only [d60806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare808 p hg
    simpa only [d60806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare810 (p : Pattern) (guard : d60807 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60806 p = 1 := by simpa only [d60807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare809 p hg
    simpa only [d60807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare811 (p : Pattern) (guard : d60808 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60807 p = 1 := by simpa only [d60808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare810 p hg
    simpa only [d60808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare812 (p : Pattern) (guard : d60809 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 135 with
  | false =>
    have hg : d60800 p = 1 := by simpa only [d60809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare803 p hg
    simpa only [d60809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare813 (p : Pattern) (guard : d60810 p = 1) : d47805 p ≤ (0 : Int) + d47757 p := by
  cases selected : p 119 with
  | false =>
    have hg : d60809 p = 1 := by simpa only [d60810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare812 p hg
    simpa only [d60810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare70 p hg
    simpa only [d60810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare814 (p : Pattern) (guard : d60811 p = 1) : d47807 p ≤ (0 : Int) + d47765 p := by
  cases selected : p 116 with
  | false =>
    have hg : d60810 p = 1 := by simpa only [d60811, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare813 p hg
    simpa only [d60811, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60811, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare74 p hg
    simpa only [d60811, d47807, d47765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare815 (p : Pattern) (guard : d60812 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 115 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60812, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare22 p hg
    simpa only [d60812, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60811 p = 1 := by simpa only [d60812, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare814 p hg
    simpa only [d60812, d47808, d47766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare816 (p : Pattern) (guard : d60813 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60804 p = 1 := by simpa only [d60813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare807 p hg
    simpa only [d60813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60812 p = 1 := by simpa only [d60813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare815 p hg
    simpa only [d60813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare817 (p : Pattern) (guard : d60814 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60813 p = 1 := by simpa only [d60814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare816 p hg
    simpa only [d60814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare818 (p : Pattern) (guard : d60815 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60814 p = 1 := by simpa only [d60815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare817 p hg
    simpa only [d60815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare819 (p : Pattern) (guard : d60816 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60815 p = 1 := by simpa only [d60816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare818 p hg
    simpa only [d60816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare820 (p : Pattern) (guard : d60817 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60808 p = 1 := by simpa only [d60817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare811 p hg
    simpa only [d60817, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60816 p = 1 := by simpa only [d60817, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare819 p hg
    simpa only [d60817, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare821 (p : Pattern) (guard : d60818 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d60817 p = 1 := by simpa only [d60818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare820 p hg
    simpa only [d60818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare822 (p : Pattern) (guard : d60819 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60816 p = 1 := by simpa only [d60819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare819 p hg
    simpa only [d60819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare823 (p : Pattern) (guard : d60820 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d60819 p = 1 := by simpa only [d60820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare822 p hg
    simpa only [d60820, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60820, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60820, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare824 (p : Pattern) (guard : d60821 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d60818 p = 1 := by simpa only [d60821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare821 p hg
    simpa only [d60821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60820 p = 1 := by simpa only [d60821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare823 p hg
    simpa only [d60821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare825 (p : Pattern) (guard : d60822 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60821 p = 1 := by simpa only [d60822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare824 p hg
    simpa only [d60822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare826 (p : Pattern) (guard : d60823 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60822 p = 1 := by simpa only [d60823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare825 p hg
    simpa only [d60823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare827 (p : Pattern) (guard : d60824 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60824, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d60824, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60823 p = 1 := by simpa only [d60824, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare826 p hg
    simpa only [d60824, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare828 (p : Pattern) (guard : d60825 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60825, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60824 p = 1 := by simpa only [d60825, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare827 p hg
    simpa only [d60825, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare829 (p : Pattern) (guard : d60826 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 113 with
  | false =>
    have hg : d60812 p = 1 := by simpa only [d60826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare815 p hg
    simpa only [d60826, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60826, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60826, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare830 (p : Pattern) (guard : d60827 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 96 with
  | false =>
    have hg : d60826 p = 1 := by simpa only [d60827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare829 p hg
    simpa only [d60827, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60827, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60827, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare831 (p : Pattern) (guard : d60828 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 95 with
  | false =>
    have hg : d60827 p = 1 := by simpa only [d60828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare830 p hg
    simpa only [d60828, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60828, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60828, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare832 (p : Pattern) (guard : d60829 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 93 with
  | false =>
    have hg : d60828 p = 1 := by simpa only [d60829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare831 p hg
    simpa only [d60829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare833 (p : Pattern) (guard : d60830 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 91 with
  | false =>
    have hg : d60829 p = 1 := by simpa only [d60830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare832 p hg
    simpa only [d60830, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60830, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60830, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare834 (p : Pattern) (guard : d60831 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 90 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60830 p = 1 := by simpa only [d60831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare833 p hg
    simpa only [d60831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare835 (p : Pattern) (guard : d60832 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 89 with
  | false =>
    have hg : d60831 p = 1 := by simpa only [d60832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare834 p hg
    simpa only [d60832, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60832, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60832, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare836 (p : Pattern) (guard : d60833 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 74 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60832 p = 1 := by simpa only [d60833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare835 p hg
    simpa only [d60833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare837 (p : Pattern) (guard : d60834 p = 1) : d47808 p ≤ (0 : Int) + d47766 p := by
  cases selected : p 73 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare21 p hg
    simpa only [d60834, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60833 p = 1 := by simpa only [d60834, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare836 p hg
    simpa only [d60834, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare838 (p : Pattern) (guard : d60835 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 71 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60835, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20 p hg
    simpa only [d60835, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60834 p = 1 := by simpa only [d60835, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare837 p hg
    simpa only [d60835, d47809, d47767, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare839 (p : Pattern) (guard : d60836 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 70 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60836, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60835 p = 1 := by simpa only [d60836, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare838 p hg
    simpa only [d60836, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare840 (p : Pattern) (guard : d60837 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 69 with
  | false =>
    have hg : d60825 p = 1 := by simpa only [d60837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare828 p hg
    simpa only [d60837, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60836 p = 1 := by simpa only [d60837, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare839 p hg
    simpa only [d60837, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare841 (p : Pattern) (guard : d60838 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 51 with
  | false =>
    have hg : d60837 p = 1 := by simpa only [d60838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare840 p hg
    simpa only [d60838, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60838, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60838, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare842 (p : Pattern) (guard : d60839 p = 1) : d47809 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 50 with
  | false =>
    have hg : d60838 p = 1 := by simpa only [d60839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare841 p hg
    simpa only [d60839, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60839, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19 p hg
    simpa only [d60839, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare843 (p : Pattern) (guard : d60840 p = 1) : d47865 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 49 with
  | false =>
    have hg : d60839 p = 1 := by simpa only [d60840, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare842 p hg
    simpa only [d60840, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d60840, d47865, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare91 p hg
    simpa only [d60840, d47865, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare844 (p : Pattern) (guard : d60841 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 48 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60841, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare18 p hg
    simpa only [d60841, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60840 p = 1 := by simpa only [d60841, d47866, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare843 p hg
    simpa only [d60841, d47866, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare845 (p : Pattern) (guard : d60842 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10260 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60842, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60841 p = 1 := by simpa only [d60842, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare844 p hg
    simpa only [d60842, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare846 (p : Pattern) (guard : d60843 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10259 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60843, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60842 p = 1 := by simpa only [d60843, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare845 p hg
    simpa only [d60843, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare847 (p : Pattern) (guard : d60844 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10258 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60844, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60843 p = 1 := by simpa only [d60844, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare846 p hg
    simpa only [d60844, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare848 (p : Pattern) (guard : d60845 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10257 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60845, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60844 p = 1 := by simpa only [d60845, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare847 p hg
    simpa only [d60845, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare849 (p : Pattern) (guard : d60846 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10256 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60846, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60845 p = 1 := by simpa only [d60846, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare848 p hg
    simpa only [d60846, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare850 (p : Pattern) (guard : d60847 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10255 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60847, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60846 p = 1 := by simpa only [d60847, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare849 p hg
    simpa only [d60847, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare851 (p : Pattern) (guard : d60848 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10254 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60848, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60847 p = 1 := by simpa only [d60848, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare850 p hg
    simpa only [d60848, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare852 (p : Pattern) (guard : d60849 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10253 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60849, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60848 p = 1 := by simpa only [d60849, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare851 p hg
    simpa only [d60849, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare853 (p : Pattern) (guard : d60850 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10252 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d60850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17 p hg
    simpa only [d60850, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60849 p = 1 := by simpa only [d60850, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare852 p hg
    simpa only [d60850, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare854 (p : Pattern) (guard : d60851 p = 1) : d47866 p ≤ (0 : Int) + d47767 p := by
  cases selected : p 10251 with
  | false =>
    have hg : d60774 p = 1 := by simpa only [d60851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare625 p hg
    simpa only [d60851, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60850 p = 1 := by simpa only [d60851, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare853 p hg
    simpa only [d60851, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare855 (p : Pattern) (guard : d1997 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare161 p hg
    simpa only [d1997, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d1997, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare856 (p : Pattern) (guard : d1998 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare857 (p : Pattern) (guard : d1999 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare856 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare858 (p : Pattern) (guard : d2000 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare857 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare859 (p : Pattern) (guard : d2001 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare635 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare860 (p : Pattern) (guard : d2002 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare859 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare861 (p : Pattern) (guard : d2003 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2002 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare860 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare862 (p : Pattern) (guard : d2004 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare858 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2003 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare861 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare863 (p : Pattern) (guard : d2005 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare635 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare864 (p : Pattern) (guard : d2006 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare863 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare865 (p : Pattern) (guard : d2007 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare864 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare866 (p : Pattern) (guard : d2008 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare865 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare867 (p : Pattern) (guard : d2009 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2004 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare862 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2008 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare866 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare868 (p : Pattern) (guard : d2010 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2009 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare869 (p : Pattern) (guard : d2011 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2010 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare868 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare870 (p : Pattern) (guard : d2012 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2011 p = 1 := by simpa only [d2012, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare869 p hg
    simpa only [d2012, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2012, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d2012, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare871 (p : Pattern) (guard : d2143 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2012 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare870 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare872 (p : Pattern) (guard : d2331 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2331, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d2331, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2143 p = 1 := by simpa only [d2331, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare871 p hg
    simpa only [d2331, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare873 (p : Pattern) (guard : d1997 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d307 p = 1 := by simpa only [d1997, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare175 p hg
    simpa only [d1997, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1997, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43 p hg
    simpa only [d1997, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare874 (p : Pattern) (guard : d1998 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1997 p = 1 := by simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare873 p hg
    simpa only [d1998, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare875 (p : Pattern) (guard : d1999 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1998 p = 1 := by simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare874 p hg
    simpa only [d1999, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare876 (p : Pattern) (guard : d2000 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1999 p = 1 := by simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare875 p hg
    simpa only [d2000, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare877 (p : Pattern) (guard : d2001 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1523 p = 1 := by simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare662 p hg
    simpa only [d2001, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare878 (p : Pattern) (guard : d2002 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2001 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare877 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2002, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare879 (p : Pattern) (guard : d2003 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2002 p = 1 := by simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare878 p hg
    simpa only [d2003, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare880 (p : Pattern) (guard : d2004 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2000 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare876 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2003 p = 1 := by simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare879 p hg
    simpa only [d2004, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare881 (p : Pattern) (guard : d2005 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1523 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare662 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2005, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare882 (p : Pattern) (guard : d2006 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2005 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare881 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2006, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare883 (p : Pattern) (guard : d2007 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2006 p = 1 := by simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d2007, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare884 (p : Pattern) (guard : d2008 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2007 p = 1 := by simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare883 p hg
    simpa only [d2008, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare885 (p : Pattern) (guard : d2009 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2004 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare880 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2008 p = 1 := by simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare884 p hg
    simpa only [d2009, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare886 (p : Pattern) (guard : d2010 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2009 p = 1 := by simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare885 p hg
    simpa only [d2010, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare887 (p : Pattern) (guard : d2011 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2010 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare886 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare888 (p : Pattern) (guard : d2012 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2011 p = 1 := by simpa only [d2012, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare887 p hg
    simpa only [d2012, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2012, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d2012, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare889 (p : Pattern) (guard : d2143 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare55 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2012 p = 1 := by simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare888 p hg
    simpa only [d2143, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare890 (p : Pattern) (guard : d2144 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2143 p = 1 := by simpa only [d2144, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare889 p hg
    simpa only [d2144, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2144, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d2144, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare891 (p : Pattern) (guard : d2332 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2331 p = 1 := by simpa only [d2332, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare872 p hg
    simpa only [d2332, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2144 p = 1 := by simpa only [d2332, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare890 p hg
    simpa only [d2332, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare892 (p : Pattern) (guard : d18309 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2332 p = 1 := by simpa only [d18309, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare891 p hg
    simpa only [d18309, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18309, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d18309, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare893 (p : Pattern) (guard : d18310 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d18309 p = 1 := by simpa only [d18310, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare892 p hg
    simpa only [d18310, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18310, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d18310, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare894 (p : Pattern) (guard : d2013 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare895 (p : Pattern) (guard : d2014 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare856 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare894 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare896 (p : Pattern) (guard : d2015 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1999 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare857 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare895 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare897 (p : Pattern) (guard : d2016 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d2016, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare98 p hg
    simpa only [d2016, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2016, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare27 p hg
    simpa only [d2016, d47630, d47715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare898 (p : Pattern) (guard : d2017 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare855 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2016 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare897 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare899 (p : Pattern) (guard : d2018 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2017 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare898 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare900 (p : Pattern) (guard : d2019 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare860 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2018 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare901 (p : Pattern) (guard : d2020 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2015 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare896 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2019 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare900 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare902 (p : Pattern) (guard : d2021 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 226 with
  | false =>
    have hg : d2016 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare897 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare903 (p : Pattern) (guard : d2022 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2021 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare902 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare904 (p : Pattern) (guard : d2023 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare864 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2022 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare903 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare905 (p : Pattern) (guard : d2024 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2023 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare904 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare906 (p : Pattern) (guard : d2025 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2020 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare901 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2024 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare905 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare907 (p : Pattern) (guard : d2026 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare867 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2025 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare906 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare908 (p : Pattern) (guard : d2027 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare894 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare909 (p : Pattern) (guard : d2028 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare908 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare910 (p : Pattern) (guard : d2029 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare909 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare911 (p : Pattern) (guard : d2030 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare910 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare912 (p : Pattern) (guard : d2031 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare911 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare913 (p : Pattern) (guard : d2032 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2026 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare907 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare912 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare914 (p : Pattern) (guard : d2033 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2032 p = 1 := by simpa only [d2033, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare913 p hg
    simpa only [d2033, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2033, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d2033, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare915 (p : Pattern) (guard : d2034 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2012 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare870 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2033 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare914 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare916 (p : Pattern) (guard : d2335 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2335, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d2335, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2034 p = 1 := by simpa only [d2335, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare915 p hg
    simpa only [d2335, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare917 (p : Pattern) (guard : d2013 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare873 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2013, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare918 (p : Pattern) (guard : d2014 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1998 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare874 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2013 p = 1 := by simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare917 p hg
    simpa only [d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare919 (p : Pattern) (guard : d2015 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1999 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare875 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2014 p = 1 := by simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare918 p hg
    simpa only [d2015, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare920 (p : Pattern) (guard : d2016 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 246 with
  | false =>
    have hg : d128 p = 1 := by simpa only [d2016, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare113 p hg
    simpa only [d2016, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2016, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43 p hg
    simpa only [d2016, d47617, d47706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare921 (p : Pattern) (guard : d2017 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d1997 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare873 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2016 p = 1 := by simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare920 p hg
    simpa only [d2017, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare922 (p : Pattern) (guard : d2018 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2017 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare921 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2018, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare923 (p : Pattern) (guard : d2019 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2002 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare878 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2018 p = 1 := by simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare922 p hg
    simpa only [d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare924 (p : Pattern) (guard : d2020 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2015 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare919 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2019 p = 1 := by simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare923 p hg
    simpa only [d2020, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare925 (p : Pattern) (guard : d2021 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 226 with
  | false =>
    have hg : d2016 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare920 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare926 (p : Pattern) (guard : d2022 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2021 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare925 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2022, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare927 (p : Pattern) (guard : d2023 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2006 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare882 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2022 p = 1 := by simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare926 p hg
    simpa only [d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare928 (p : Pattern) (guard : d2024 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2023 p = 1 := by simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare927 p hg
    simpa only [d2024, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare929 (p : Pattern) (guard : d2025 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2020 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare924 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2024 p = 1 := by simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare928 p hg
    simpa only [d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare930 (p : Pattern) (guard : d2026 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2009 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare885 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2025 p = 1 := by simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare929 p hg
    simpa only [d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare931 (p : Pattern) (guard : d2027 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 225 with
  | false =>
    have hg : d2013 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare917 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2027, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare932 (p : Pattern) (guard : d2028 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare931 p hg
    simpa only [d2028, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare933 (p : Pattern) (guard : d2029 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2028 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare932 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare934 (p : Pattern) (guard : d2030 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2029 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare933 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare935 (p : Pattern) (guard : d2031 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2030 p = 1 := by simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare934 p hg
    simpa only [d2031, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare936 (p : Pattern) (guard : d2032 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2026 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare930 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2031 p = 1 := by simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare935 p hg
    simpa only [d2032, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare937 (p : Pattern) (guard : d2033 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2032 p = 1 := by simpa only [d2033, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare936 p hg
    simpa only [d2033, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2033, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d2033, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare938 (p : Pattern) (guard : d2034 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2012 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare888 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2033 p = 1 := by simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare937 p hg
    simpa only [d2034, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare939 (p : Pattern) (guard : d2035 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2034 p = 1 := by simpa only [d2035, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare938 p hg
    simpa only [d2035, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2035, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d2035, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare940 (p : Pattern) (guard : d2336 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2335 p = 1 := by simpa only [d2336, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare916 p hg
    simpa only [d2336, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2035 p = 1 := by simpa only [d2336, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare939 p hg
    simpa only [d2336, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare941 (p : Pattern) (guard : d18318 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2336 p = 1 := by simpa only [d18318, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare940 p hg
    simpa only [d18318, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18318, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d18318, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare942 (p : Pattern) (guard : d18319 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d18318 p = 1 := by simpa only [d18319, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare941 p hg
    simpa only [d18319, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18319, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d18319, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare943 (p : Pattern) (guard : d60852 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d18310 p = 1 := by simpa only [d60852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare893 p hg
    simpa only [d60852, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18319 p = 1 := by simpa only [d60852, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare942 p hg
    simpa only [d60852, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare944 (p : Pattern) (guard : d2039 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare895 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare908 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare945 (p : Pattern) (guard : d2040 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2018 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare899 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare946 (p : Pattern) (guard : d2041 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2039 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare944 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare945 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare947 (p : Pattern) (guard : d2042 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2022 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare903 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare948 (p : Pattern) (guard : d2043 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2042 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare947 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare949 (p : Pattern) (guard : d2044 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2041 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare946 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare948 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare950 (p : Pattern) (guard : d2045 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare906 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2044 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare951 (p : Pattern) (guard : d2046 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2027 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare908 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare952 (p : Pattern) (guard : d2047 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2046 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare951 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare953 (p : Pattern) (guard : d2048 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2047 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare952 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare954 (p : Pattern) (guard : d2049 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare911 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare953 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare955 (p : Pattern) (guard : d2050 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2045 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare950 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare954 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare956 (p : Pattern) (guard : d2051 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2050 p = 1 := by simpa only [d2051, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare955 p hg
    simpa only [d2051, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2051, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d2051, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare957 (p : Pattern) (guard : d2052 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare914 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2051 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare956 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare958 (p : Pattern) (guard : d2340 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2340, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d2340, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2052 p = 1 := by simpa only [d2340, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare957 p hg
    simpa only [d2340, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare959 (p : Pattern) (guard : d2039 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2014 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare918 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2027 p = 1 := by simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare931 p hg
    simpa only [d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare960 (p : Pattern) (guard : d2040 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2018 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare922 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2040, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare961 (p : Pattern) (guard : d2041 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2039 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare959 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare960 p hg
    simpa only [d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare962 (p : Pattern) (guard : d2042 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2022 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare926 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2042, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare963 (p : Pattern) (guard : d2043 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2042 p = 1 := by simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare962 p hg
    simpa only [d2043, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare964 (p : Pattern) (guard : d2044 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2041 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare961 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare963 p hg
    simpa only [d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare965 (p : Pattern) (guard : d2045 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2025 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare929 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2044 p = 1 := by simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare964 p hg
    simpa only [d2045, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare966 (p : Pattern) (guard : d2046 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 224 with
  | false =>
    have hg : d2027 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare931 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2046, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare967 (p : Pattern) (guard : d2047 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d2046 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare966 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare968 (p : Pattern) (guard : d2048 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2047 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare967 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare969 (p : Pattern) (guard : d2049 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2030 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare934 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare968 p hg
    simpa only [d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare970 (p : Pattern) (guard : d2050 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2045 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare965 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2049 p = 1 := by simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare969 p hg
    simpa only [d2050, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare971 (p : Pattern) (guard : d2051 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2050 p = 1 := by simpa only [d2051, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare970 p hg
    simpa only [d2051, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2051, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d2051, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare972 (p : Pattern) (guard : d2052 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2033 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare937 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2051 p = 1 := by simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare971 p hg
    simpa only [d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare973 (p : Pattern) (guard : d2053 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2052 p = 1 := by simpa only [d2053, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare972 p hg
    simpa only [d2053, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2053, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d2053, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare974 (p : Pattern) (guard : d2341 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2340 p = 1 := by simpa only [d2341, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare958 p hg
    simpa only [d2341, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2053 p = 1 := by simpa only [d2341, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare973 p hg
    simpa only [d2341, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare975 (p : Pattern) (guard : d18336 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2341 p = 1 := by simpa only [d18336, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare974 p hg
    simpa only [d18336, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18336, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d18336, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare976 (p : Pattern) (guard : d18337 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d18336 p = 1 := by simpa only [d18337, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare975 p hg
    simpa only [d18337, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18337, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d18337, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare977 (p : Pattern) (guard : d60853 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d18319 p = 1 := by simpa only [d60853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare942 p hg
    simpa only [d60853, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18337 p = 1 := by simpa only [d60853, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare976 p hg
    simpa only [d60853, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare978 (p : Pattern) (guard : d60854 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60852 p = 1 := by simpa only [d60854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare943 p hg
    simpa only [d60854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60853 p = 1 := by simpa only [d60854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare977 p hg
    simpa only [d60854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare979 (p : Pattern) (guard : d2058 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare945 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare980 (p : Pattern) (guard : d2059 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2058 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare979 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare948 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare981 (p : Pattern) (guard : d2060 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare980 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare953 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare982 (p : Pattern) (guard : d2061 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2048 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare953 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare983 (p : Pattern) (guard : d2062 p = 1) : d47630 p ≤ (0 : Int) + d47715 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2060 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare981 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare982 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare984 (p : Pattern) (guard : d2063 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2062 p = 1 := by simpa only [d2063, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare983 p hg
    simpa only [d2063, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2063, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37 p hg
    simpa only [d2063, d47652, d47731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare985 (p : Pattern) (guard : d2064 p = 1) : d47652 p ≤ (0 : Int) + d47731 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare956 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2063 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare984 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare986 (p : Pattern) (guard : d2346 p = 1) : d47652 p ≤ (0 : Int) + d47732 p := by
  cases selected : p 163 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2346, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25 p hg
    simpa only [d2346, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2064 p = 1 := by simpa only [d2346, d47732, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare985 p hg
    simpa only [d2346, d47732, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare987 (p : Pattern) (guard : d2058 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 223 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2040 p = 1 := by simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare960 p hg
    simpa only [d2058, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare988 (p : Pattern) (guard : d2059 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 204 with
  | false =>
    have hg : d2058 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare987 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2043 p = 1 := by simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare963 p hg
    simpa only [d2059, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare989 (p : Pattern) (guard : d2060 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2059 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare988 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2048 p = 1 := by simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare968 p hg
    simpa only [d2060, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare990 (p : Pattern) (guard : d2061 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 202 with
  | false =>
    have hg : d2048 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare968 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare45 p hg
    simpa only [d2061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare991 (p : Pattern) (guard : d2062 p = 1) : d47617 p ≤ (0 : Int) + d47706 p := by
  cases selected : p 201 with
  | false =>
    have hg : d2060 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare989 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2061 p = 1 := by simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare990 p hg
    simpa only [d2062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare992 (p : Pattern) (guard : d2063 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 182 with
  | false =>
    have hg : d2062 p = 1 := by simpa only [d2063, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare991 p hg
    simpa only [d2063, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2063, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare53 p hg
    simpa only [d2063, d47619, d47708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare993 (p : Pattern) (guard : d2064 p = 1) : d47619 p ≤ (0 : Int) + d47708 p := by
  cases selected : p 180 with
  | false =>
    have hg : d2051 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare971 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2063 p = 1 := by simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare992 p hg
    simpa only [d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare994 (p : Pattern) (guard : d2065 p = 1) : d47797 p ≤ (0 : Int) + d47733 p := by
  cases selected : p 163 with
  | false =>
    have hg : d2064 p = 1 := by simpa only [d2065, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare993 p hg
    simpa only [d2065, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d2065, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare57 p hg
    simpa only [d2065, d47797, d47733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare995 (p : Pattern) (guard : d2347 p = 1) : d47798 p ≤ (0 : Int) + d47734 p := by
  cases selected : p 162 with
  | false =>
    have hg : d2346 p = 1 := by simpa only [d2347, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare986 p hg
    simpa only [d2347, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d2065 p = 1 := by simpa only [d2347, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare994 p hg
    simpa only [d2347, d47798, d47734, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare996 (p : Pattern) (guard : d18369 p = 1) : d47799 p ≤ (0 : Int) + d47737 p := by
  cases selected : p 161 with
  | false =>
    have hg : d2347 p = 1 := by simpa only [d18369, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare995 p hg
    simpa only [d18369, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18369, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare60 p hg
    simpa only [d18369, d47799, d47737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare997 (p : Pattern) (guard : d18370 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 160 with
  | false =>
    have hg : d18369 p = 1 := by simpa only [d18370, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare996 p hg
    simpa only [d18370, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d18370, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare62 p hg
    simpa only [d18370, d47803, d47755, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare998 (p : Pattern) (guard : d60855 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 159 with
  | false =>
    have hg : d18337 p = 1 := by simpa only [d60855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare976 p hg
    simpa only [d60855, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d18370 p = 1 := by simpa only [d60855, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare997 p hg
    simpa only [d60855, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare999 (p : Pattern) (guard : d60856 p = 1) : d47803 p ≤ (0 : Int) + d47755 p := by
  cases selected : p 158 with
  | false =>
    have hg : d60853 p = 1 := by simpa only [d60856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare977 p hg
    simpa only [d60856, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d60855 p = 1 := by simpa only [d60856, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare998 p hg
    simpa only [d60856, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Soko22Hazard87
