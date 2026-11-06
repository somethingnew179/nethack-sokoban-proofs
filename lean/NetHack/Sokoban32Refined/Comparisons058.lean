/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban32Refined.Comparisons057
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban32Refined
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare8120 (p : Pattern) (guard : d1505 p = 1) : d11 p ≤ (2 : Int) + d10 p := by
  cases selected : p 159 with
  | false =>
    have hg : d0 p = 1 := by simpa only [d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8117 p hg
    simpa only [d1505, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d917 p = 1 := by simpa only [d1505, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8119 p hg
    simpa only [d1505, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8121 (p : Pattern) (guard : d0 p = 1) : d39 p ≤ (2 : Int) + d10 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8122 (p : Pattern) (guard : d1506 p = 1) : d698 p ≤ (2 : Int) + d10 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1505 p = 1 := by simpa only [d1506, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8120 p hg
    simpa only [d1506, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1506, d698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8121 p hg
    simpa only [d1506, d698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8123 (p : Pattern) (guard : d1506 p = 1) : d699 p ≤ (2 : Int) + d1772 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d699, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8116 p hg
    simpa only [d699, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d699, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8122 p hg
    simpa only [d699, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8124 (p : Pattern) (guard : d1506 p = 1) : d700 p ≤ (2 : Int) + d1773 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d700, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8116 p hg
    simpa only [d700, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d700, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8123 p hg
    simpa only [d700, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8125 (p : Pattern) (guard : d1506 p = 1) : d2 p ≤ (2 : Int) + d2 p := by
  omega
theorem compare8126 (p : Pattern) (guard : d1506 p = 1) : d701 p ≤ (2 : Int) + d1774 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d701, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8116 p hg
    simpa only [d701, d1774, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d701, d1774, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8125 p hg
    simpa only [d701, d1774, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8127 (p : Pattern) (guard : d1506 p = 1) : d702 p ≤ (2 : Int) + d1775 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d702, d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8123 p hg
    simpa only [d702, d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d702, d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8126 p hg
    simpa only [d702, d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8128 (p : Pattern) (guard : d1506 p = 1) : d703 p ≤ (2 : Int) + d1776 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d703, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8123 p hg
    simpa only [d703, d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d703, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8127 p hg
    simpa only [d703, d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8129 (p : Pattern) (guard : d1506 p = 1) : d704 p ≤ (2 : Int) + d1777 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d704, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8124 p hg
    simpa only [d704, d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d704, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8128 p hg
    simpa only [d704, d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8130 (p : Pattern) (guard : d1506 p = 1) : d705 p ≤ (2 : Int) + d1778 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d705, d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8122 p hg
    simpa only [d705, d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d705, d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8125 p hg
    simpa only [d705, d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8131 (p : Pattern) (guard : d1506 p = 1) : d706 p ≤ (2 : Int) + d1779 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d706, d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8122 p hg
    simpa only [d706, d1779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d706, d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8130 p hg
    simpa only [d706, d1779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8132 (p : Pattern) (guard : d1506 p = 1) : d707 p ≤ (2 : Int) + d1780 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d707, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8124 p hg
    simpa only [d707, d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d707, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8131 p hg
    simpa only [d707, d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8133 (p : Pattern) (guard : d1506 p = 1) : d708 p ≤ (2 : Int) + d1781 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d708, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8124 p hg
    simpa only [d708, d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d708, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8132 p hg
    simpa only [d708, d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8134 (p : Pattern) (guard : d1506 p = 1) : d709 p ≤ (2 : Int) + d1782 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d709, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8124 p hg
    simpa only [d709, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d709, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8130 p hg
    simpa only [d709, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8135 (p : Pattern) (guard : d1506 p = 1) : d710 p ≤ (2 : Int) + d1783 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d710, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8124 p hg
    simpa only [d710, d1783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d710, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8134 p hg
    simpa only [d710, d1783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8136 (p : Pattern) (guard : d1506 p = 1) : d711 p ≤ (2 : Int) + d1784 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d711, d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8133 p hg
    simpa only [d711, d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d711, d1784, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8135 p hg
    simpa only [d711, d1784, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8137 (p : Pattern) (guard : d1506 p = 1) : d712 p ≤ (2 : Int) + d1785 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d712, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8123 p hg
    simpa only [d712, d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d712, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8130 p hg
    simpa only [d712, d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8138 (p : Pattern) (guard : d1506 p = 1) : d713 p ≤ (2 : Int) + d1786 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d713, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8123 p hg
    simpa only [d713, d1786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d713, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8137 p hg
    simpa only [d713, d1786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8139 (p : Pattern) (guard : d1506 p = 1) : d714 p ≤ (2 : Int) + d1787 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d714, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8127 p hg
    simpa only [d714, d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d714, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8130 p hg
    simpa only [d714, d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8140 (p : Pattern) (guard : d1506 p = 1) : d715 p ≤ (2 : Int) + d1788 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d715, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8127 p hg
    simpa only [d715, d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d715, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8139 p hg
    simpa only [d715, d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8141 (p : Pattern) (guard : d1506 p = 1) : d716 p ≤ (2 : Int) + d1789 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d716, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8138 p hg
    simpa only [d716, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d716, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8140 p hg
    simpa only [d716, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8142 (p : Pattern) (guard : d1506 p = 1) : d717 p ≤ (2 : Int) + d1790 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d717, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8136 p hg
    simpa only [d717, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d717, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8141 p hg
    simpa only [d717, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8143 (p : Pattern) (guard : d1506 p = 1) : d718 p ≤ (2 : Int) + d1791 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d718, d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8129 p hg
    simpa only [d718, d1791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d718, d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8142 p hg
    simpa only [d718, d1791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8144 (p : Pattern) (guard : d1506 p = 1) : d719 p ≤ (2 : Int) + d1792 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d719, d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8116 p hg
    simpa only [d719, d1792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d719, d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8126 p hg
    simpa only [d719, d1792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8145 (p : Pattern) (guard : d1506 p = 1) : d720 p ≤ (2 : Int) + d1793 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d720, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8124 p hg
    simpa only [d720, d1793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d720, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8144 p hg
    simpa only [d720, d1793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8146 (p : Pattern) (guard : d1506 p = 1) : d721 p ≤ (2 : Int) + d1794 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d721, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8145 p hg
    simpa only [d721, d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d721, d1794, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8131 p hg
    simpa only [d721, d1794, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8147 (p : Pattern) (guard : d1506 p = 1) : d722 p ≤ (2 : Int) + d1795 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d722, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8144 p hg
    simpa only [d722, d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d722, d1795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8130 p hg
    simpa only [d722, d1795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8148 (p : Pattern) (guard : d1506 p = 1) : d723 p ≤ (2 : Int) + d1796 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d723, d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8144 p hg
    simpa only [d723, d1796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d723, d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8147 p hg
    simpa only [d723, d1796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8149 (p : Pattern) (guard : d1506 p = 1) : d724 p ≤ (2 : Int) + d1797 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d724, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8135 p hg
    simpa only [d724, d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d724, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8148 p hg
    simpa only [d724, d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8150 (p : Pattern) (guard : d1506 p = 1) : d725 p ≤ (2 : Int) + d1798 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d725, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8131 p hg
    simpa only [d725, d1798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d725, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8125 p hg
    simpa only [d725, d1798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8151 (p : Pattern) (guard : d1506 p = 1) : d726 p ≤ (2 : Int) + d1799 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d726, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8131 p hg
    simpa only [d726, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d726, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8150 p hg
    simpa only [d726, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8152 (p : Pattern) (guard : d1506 p = 1) : d727 p ≤ (2 : Int) + d1800 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d727, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8130 p hg
    simpa only [d727, d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d727, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8125 p hg
    simpa only [d727, d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8153 (p : Pattern) (guard : d1506 p = 1) : d728 p ≤ (2 : Int) + d1801 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d728, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8130 p hg
    simpa only [d728, d1801, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d728, d1801, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8152 p hg
    simpa only [d728, d1801, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8154 (p : Pattern) (guard : d1506 p = 1) : d729 p ≤ (2 : Int) + d1802 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d729, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8151 p hg
    simpa only [d729, d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d729, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8153 p hg
    simpa only [d729, d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8155 (p : Pattern) (guard : d1506 p = 1) : d730 p ≤ (2 : Int) + d1803 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d730, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8149 p hg
    simpa only [d730, d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d730, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8154 p hg
    simpa only [d730, d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8156 (p : Pattern) (guard : d1506 p = 1) : d731 p ≤ (2 : Int) + d1804 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d731, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8146 p hg
    simpa only [d731, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d731, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8155 p hg
    simpa only [d731, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8157 (p : Pattern) (guard : d1506 p = 1) : d732 p ≤ (2 : Int) + d1805 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d732, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8143 p hg
    simpa only [d732, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d732, d1805, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8156 p hg
    simpa only [d732, d1805, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8158 (p : Pattern) (guard : d1506 p = 1) : d733 p ≤ (2 : Int) + d1806 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d733, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8135 p hg
    simpa only [d733, d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d733, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8141 p hg
    simpa only [d733, d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8159 (p : Pattern) (guard : d1506 p = 1) : d734 p ≤ (2 : Int) + d1807 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d734, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8129 p hg
    simpa only [d734, d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d734, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8158 p hg
    simpa only [d734, d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8160 (p : Pattern) (guard : d1506 p = 1) : d735 p ≤ (2 : Int) + d1808 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d735, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8131 p hg
    simpa only [d735, d1808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d735, d1808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8130 p hg
    simpa only [d735, d1808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8161 (p : Pattern) (guard : d1506 p = 1) : d736 p ≤ (2 : Int) + d1809 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d736, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8145 p hg
    simpa only [d736, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d736, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8160 p hg
    simpa only [d736, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8162 (p : Pattern) (guard : d1506 p = 1) : d737 p ≤ (2 : Int) + d1810 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d737, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8135 p hg
    simpa only [d737, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d737, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8140 p hg
    simpa only [d737, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8163 (p : Pattern) (guard : d1506 p = 1) : d738 p ≤ (2 : Int) + d1811 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d738, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8153 p hg
    simpa only [d738, d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d738, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8125 p hg
    simpa only [d738, d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8164 (p : Pattern) (guard : d1506 p = 1) : d739 p ≤ (2 : Int) + d1812 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d739, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8162 p hg
    simpa only [d739, d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d739, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8163 p hg
    simpa only [d739, d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8165 (p : Pattern) (guard : d1506 p = 1) : d740 p ≤ (2 : Int) + d1813 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d740, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8161 p hg
    simpa only [d740, d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d740, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8164 p hg
    simpa only [d740, d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8166 (p : Pattern) (guard : d1506 p = 1) : d741 p ≤ (2 : Int) + d1814 p := by
  cases selected : p 86 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d741, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8159 p hg
    simpa only [d741, d1814, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d741, d1814, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8165 p hg
    simpa only [d741, d1814, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8167 (p : Pattern) (guard : d1506 p = 1) : d742 p ≤ (2 : Int) + d1815 p := by
  cases selected : p 80 with
  | false =>
    have hg : d1506 p = 1 := by simpa only [d742, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8157 p hg
    simpa only [d742, d1815, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1506 p = 1 := by simpa only [d742, d1815, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8166 p hg
    simpa only [d742, d1815, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8168 (p : Pattern) (guard : d1293 p = 1) : d5 p ≤ (0 : Int) + d4 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d5, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1213 p hg
    simpa only [d1293, d5, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d5, d4, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare967 p hg
    simpa only [d1293, d5, d4, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8169 (p : Pattern) (guard : d1293 p = 1) : d5 p ≤ (0 : Int) + d6 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8168 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4471 p hg
    simpa only [d6, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8170 (p : Pattern) (guard : d1293 p = 1) : d37 p ≤ (0 : Int) + d7 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d37, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8168 p hg
    simpa only [d37, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d37, d7, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d37, d7, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8171 (p : Pattern) (guard : d1293 p = 1) : d697 p ≤ (0 : Int) + d8 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d697, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8169 p hg
    simpa only [d697, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d697, d8, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8170 p hg
    simpa only [d697, d8, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8172 (p : Pattern) (guard : d1293 p = 1) : d11 p ≤ (0 : Int) + d10 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1221 p hg
    simpa only [d1293, d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare974 p hg
    simpa only [d1293, d11, d10, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8173 (p : Pattern) (guard : d1293 p = 1) : d11 p ≤ (0 : Int) + d12 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8172 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4477 p hg
    simpa only [d12, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8174 (p : Pattern) (guard : d1293 p = 1) : d39 p ≤ (0 : Int) + d13 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d39, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8172 p hg
    simpa only [d39, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d39, d13, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d39, d13, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8175 (p : Pattern) (guard : d1293 p = 1) : d698 p ≤ (0 : Int) + d14 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d698, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8173 p hg
    simpa only [d698, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d698, d14, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8174 p hg
    simpa only [d698, d14, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8176 (p : Pattern) (guard : d1293 p = 1) : d699 p ≤ (0 : Int) + d15 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d699, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8171 p hg
    simpa only [d699, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d699, d15, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8175 p hg
    simpa only [d699, d15, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8177 (p : Pattern) (guard : d1293 p = 1) : d700 p ≤ (0 : Int) + d16 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d700, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8171 p hg
    simpa only [d700, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d700, d16, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8176 p hg
    simpa only [d700, d16, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8178 (p : Pattern) (guard : d1294 p = 1) : d700 p ≤ (0 : Int) + d16 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7694 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8177 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8179 (p : Pattern) (guard : d1293 p = 1) : d5 p ≤ (0 : Int) + d18 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8168 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7883 p hg
    simpa only [d18, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8180 (p : Pattern) (guard : d1293 p = 1) : d697 p ≤ (0 : Int) + d20 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d697, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8179 p hg
    simpa only [d697, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d697, d20, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7894 p hg
    simpa only [d697, d20, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8181 (p : Pattern) (guard : d1293 p = 1) : d11 p ≤ (0 : Int) + d22 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8172 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7888 p hg
    simpa only [d22, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8182 (p : Pattern) (guard : d1293 p = 1) : d698 p ≤ (0 : Int) + d24 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d698, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8181 p hg
    simpa only [d698, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d698, d24, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7896 p hg
    simpa only [d698, d24, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8183 (p : Pattern) (guard : d1293 p = 1) : d699 p ≤ (0 : Int) + d25 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d699, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8180 p hg
    simpa only [d699, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d699, d25, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8182 p hg
    simpa only [d699, d25, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8184 (p : Pattern) (guard : d1293 p = 1) : d700 p ≤ (0 : Int) + d26 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d700, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8180 p hg
    simpa only [d700, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d700, d26, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8183 p hg
    simpa only [d700, d26, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8185 (p : Pattern) (guard : d1294 p = 1) : d700 p ≤ (0 : Int) + d27 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7694 p hg
    simpa only [d1294, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d27, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8184 p hg
    simpa only [d1294, d27, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8186 (p : Pattern) (guard : d1294 p = 1) : d700 p ≤ (0 : Int) + d28 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8178 p hg
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8185 p hg
    simpa only [d28, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8187 (p : Pattern) (guard : d0 p = 1) : d0 p ≤ (0 : Int) + d1 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare8188 (p : Pattern) (guard : d985 p = 1) : d0 p ≤ (0 : Int) + d29 p := by
  cases selected : p 161 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare103 p hg
    simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8187 p hg
    simpa only [d985, d29, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8189 (p : Pattern) (guard : d1293 p = 1) : d5 p ≤ (0 : Int) + d30 p := by
  cases selected : p 160 with
  | false =>
    have hg : d985 p = 1 := by simpa only [d1293, d5, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8188 p hg
    simpa only [d1293, d5, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d1293, d5, d30, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare949 p hg
    simpa only [d1293, d5, d30, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8190 (p : Pattern) (guard : d1293 p = 1) : d5 p ≤ (0 : Int) + d31 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8168 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8189 p hg
    simpa only [d31, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8191 (p : Pattern) (guard : d1293 p = 1) : d37 p ≤ (0 : Int) + d32 p := by
  cases selected : p 159 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d37, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8189 p hg
    simpa only [d37, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d37, d32, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d37, d32, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8192 (p : Pattern) (guard : d1293 p = 1) : d697 p ≤ (0 : Int) + d33 p := by
  cases selected : p 158 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d697, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8190 p hg
    simpa only [d697, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d697, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8191 p hg
    simpa only [d697, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8193 (p : Pattern) (guard : d1293 p = 1) : d699 p ≤ (0 : Int) + d34 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d699, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8192 p hg
    simpa only [d699, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d699, d34, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8182 p hg
    simpa only [d699, d34, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8194 (p : Pattern) (guard : d1293 p = 1) : d700 p ≤ (0 : Int) + d35 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d700, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8192 p hg
    simpa only [d700, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d700, d35, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8193 p hg
    simpa only [d700, d35, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8195 (p : Pattern) (guard : d1294 p = 1) : d700 p ≤ (0 : Int) + d36 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7694 p hg
    simpa only [d1294, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d36, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8194 p hg
    simpa only [d1294, d36, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8196 (p : Pattern) (guard : d1294 p = 1) : d700 p ≤ (0 : Int) + d43 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7700 p hg
    simpa only [d1294, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d43, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8184 p hg
    simpa only [d1294, d43, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8197 (p : Pattern) (guard : d1294 p = 1) : d700 p ≤ (0 : Int) + d44 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8195 p hg
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8196 p hg
    simpa only [d44, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8198 (p : Pattern) (guard : d1294 p = 1) : d700 p ≤ (0 : Int) + d45 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8186 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8197 p hg
    simpa only [d45, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8199 (p : Pattern) (guard : d1294 p = 1) : d699 p ≤ (0 : Int) + d15 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7693 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8176 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8200 (p : Pattern) (guard : d1294 p = 1) : d699 p ≤ (0 : Int) + d46 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7693 p hg
    simpa only [d1294, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d46, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8183 p hg
    simpa only [d1294, d46, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8201 (p : Pattern) (guard : d1294 p = 1) : d699 p ≤ (0 : Int) + d47 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8199 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8200 p hg
    simpa only [d47, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8202 (p : Pattern) (guard : d1294 p = 1) : d699 p ≤ (0 : Int) + d48 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7693 p hg
    simpa only [d1294, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d48, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8193 p hg
    simpa only [d1294, d48, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8203 (p : Pattern) (guard : d1294 p = 1) : d699 p ≤ (0 : Int) + d49 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7699 p hg
    simpa only [d1294, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d49, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8183 p hg
    simpa only [d1294, d49, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8204 (p : Pattern) (guard : d1294 p = 1) : d699 p ≤ (0 : Int) + d50 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8202 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8203 p hg
    simpa only [d50, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8205 (p : Pattern) (guard : d1294 p = 1) : d699 p ≤ (0 : Int) + d51 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8201 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8204 p hg
    simpa only [d51, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8206 (p : Pattern) (guard : d1293 p = 1) : d701 p ≤ (0 : Int) + d52 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8171 p hg
    simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d701, d52, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8207 (p : Pattern) (guard : d1293 p = 1) : d702 p ≤ (0 : Int) + d53 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8176 p hg
    simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8206 p hg
    simpa only [d702, d53, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8208 (p : Pattern) (guard : d1294 p = 1) : d702 p ≤ (0 : Int) + d53 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7710 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8207 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8209 (p : Pattern) (guard : d1293 p = 1) : d701 p ≤ (0 : Int) + d54 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d701, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8180 p hg
    simpa only [d701, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d701, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d701, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8210 (p : Pattern) (guard : d1293 p = 1) : d702 p ≤ (0 : Int) + d55 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d702, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8183 p hg
    simpa only [d702, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d702, d55, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8209 p hg
    simpa only [d702, d55, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8211 (p : Pattern) (guard : d1294 p = 1) : d702 p ≤ (0 : Int) + d56 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7710 p hg
    simpa only [d1294, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d56, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8210 p hg
    simpa only [d1294, d56, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8212 (p : Pattern) (guard : d1294 p = 1) : d702 p ≤ (0 : Int) + d57 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8208 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8211 p hg
    simpa only [d57, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8213 (p : Pattern) (guard : d1293 p = 1) : d701 p ≤ (0 : Int) + d58 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d701, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8192 p hg
    simpa only [d701, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d701, d58, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d701, d58, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8214 (p : Pattern) (guard : d1293 p = 1) : d702 p ≤ (0 : Int) + d59 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d702, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8193 p hg
    simpa only [d702, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d702, d59, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8213 p hg
    simpa only [d702, d59, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8215 (p : Pattern) (guard : d1294 p = 1) : d702 p ≤ (0 : Int) + d60 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7710 p hg
    simpa only [d1294, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d60, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8214 p hg
    simpa only [d1294, d60, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8216 (p : Pattern) (guard : d1294 p = 1) : d702 p ≤ (0 : Int) + d63 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7714 p hg
    simpa only [d1294, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d63, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8210 p hg
    simpa only [d1294, d63, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8217 (p : Pattern) (guard : d1294 p = 1) : d702 p ≤ (0 : Int) + d64 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8215 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8216 p hg
    simpa only [d64, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8218 (p : Pattern) (guard : d1294 p = 1) : d702 p ≤ (0 : Int) + d65 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8212 p hg
    simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8217 p hg
    simpa only [d65, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8219 (p : Pattern) (guard : d1294 p = 1) : d703 p ≤ (0 : Int) + d66 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d703, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8205 p hg
    simpa only [d703, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d703, d66, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8218 p hg
    simpa only [d703, d66, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8220 (p : Pattern) (guard : d1294 p = 1) : d704 p ≤ (0 : Int) + d67 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d704, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8198 p hg
    simpa only [d704, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d704, d67, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8219 p hg
    simpa only [d704, d67, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8221 (p : Pattern) (guard : d1293 p = 1) : d705 p ≤ (0 : Int) + d70 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d705, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8182 p hg
    simpa only [d705, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d705, d70, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d705, d70, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8222 (p : Pattern) (guard : d1293 p = 1) : d706 p ≤ (0 : Int) + d71 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d706, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8182 p hg
    simpa only [d706, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d706, d71, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8221 p hg
    simpa only [d706, d71, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8223 (p : Pattern) (guard : d1294 p = 1) : d706 p ≤ (0 : Int) + d72 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7721 p hg
    simpa only [d1294, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d72, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8222 p hg
    simpa only [d1294, d72, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8224 (p : Pattern) (guard : d1294 p = 1) : d707 p ≤ (0 : Int) + d73 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d707, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8185 p hg
    simpa only [d707, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d707, d73, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8223 p hg
    simpa only [d707, d73, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8225 (p : Pattern) (guard : d1294 p = 1) : d708 p ≤ (0 : Int) + d74 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d708, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8186 p hg
    simpa only [d708, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d708, d74, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8224 p hg
    simpa only [d708, d74, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8226 (p : Pattern) (guard : d1294 p = 1) : d705 p ≤ (0 : Int) + d75 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7720 p hg
    simpa only [d1294, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d75, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8221 p hg
    simpa only [d1294, d75, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8227 (p : Pattern) (guard : d1294 p = 1) : d709 p ≤ (0 : Int) + d76 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d709, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8185 p hg
    simpa only [d709, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d709, d76, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8226 p hg
    simpa only [d709, d76, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8228 (p : Pattern) (guard : d1294 p = 1) : d710 p ≤ (0 : Int) + d77 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d710, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8186 p hg
    simpa only [d710, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d710, d77, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8227 p hg
    simpa only [d710, d77, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8229 (p : Pattern) (guard : d1294 p = 1) : d711 p ≤ (0 : Int) + d78 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d711, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8225 p hg
    simpa only [d711, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d711, d78, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8228 p hg
    simpa only [d711, d78, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8230 (p : Pattern) (guard : d1294 p = 1) : d712 p ≤ (0 : Int) + d79 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d712, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8200 p hg
    simpa only [d712, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d712, d79, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8226 p hg
    simpa only [d712, d79, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8231 (p : Pattern) (guard : d1294 p = 1) : d713 p ≤ (0 : Int) + d80 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d713, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8201 p hg
    simpa only [d713, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d713, d80, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8230 p hg
    simpa only [d713, d80, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8232 (p : Pattern) (guard : d1294 p = 1) : d714 p ≤ (0 : Int) + d81 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d714, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8211 p hg
    simpa only [d714, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d714, d81, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8226 p hg
    simpa only [d714, d81, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8233 (p : Pattern) (guard : d1294 p = 1) : d715 p ≤ (0 : Int) + d82 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d715, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8212 p hg
    simpa only [d715, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d715, d82, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8232 p hg
    simpa only [d715, d82, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8234 (p : Pattern) (guard : d1294 p = 1) : d716 p ≤ (0 : Int) + d83 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d716, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8231 p hg
    simpa only [d716, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d716, d83, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8233 p hg
    simpa only [d716, d83, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8235 (p : Pattern) (guard : d1294 p = 1) : d717 p ≤ (0 : Int) + d84 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d717, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8229 p hg
    simpa only [d717, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d717, d84, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8234 p hg
    simpa only [d717, d84, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8236 (p : Pattern) (guard : d1294 p = 1) : d718 p ≤ (0 : Int) + d85 p := by
  cases selected : p 106 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d718, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8220 p hg
    simpa only [d718, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d718, d85, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8235 p hg
    simpa only [d718, d85, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8237 (p : Pattern) (guard : d1293 p = 1) : d719 p ≤ (0 : Int) + d86 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d719, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8171 p hg
    simpa only [d719, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d719, d86, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8206 p hg
    simpa only [d719, d86, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8238 (p : Pattern) (guard : d1294 p = 1) : d719 p ≤ (0 : Int) + d86 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7738 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8237 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8239 (p : Pattern) (guard : d1293 p = 1) : d719 p ≤ (0 : Int) + d87 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d719, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8180 p hg
    simpa only [d719, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d719, d87, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8209 p hg
    simpa only [d719, d87, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8240 (p : Pattern) (guard : d1294 p = 1) : d719 p ≤ (0 : Int) + d88 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7738 p hg
    simpa only [d1294, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d88, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8239 p hg
    simpa only [d1294, d88, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8241 (p : Pattern) (guard : d1294 p = 1) : d719 p ≤ (0 : Int) + d89 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8238 p hg
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8240 p hg
    simpa only [d89, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8242 (p : Pattern) (guard : d1293 p = 1) : d719 p ≤ (0 : Int) + d90 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d719, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8192 p hg
    simpa only [d719, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d719, d90, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8213 p hg
    simpa only [d719, d90, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8243 (p : Pattern) (guard : d1294 p = 1) : d719 p ≤ (0 : Int) + d91 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7738 p hg
    simpa only [d1294, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d91, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8242 p hg
    simpa only [d1294, d91, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8244 (p : Pattern) (guard : d1294 p = 1) : d719 p ≤ (0 : Int) + d93 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7741 p hg
    simpa only [d1294, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d93, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8239 p hg
    simpa only [d1294, d93, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8245 (p : Pattern) (guard : d1294 p = 1) : d719 p ≤ (0 : Int) + d94 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8243 p hg
    simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8244 p hg
    simpa only [d94, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8246 (p : Pattern) (guard : d1294 p = 1) : d719 p ≤ (0 : Int) + d95 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8241 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8245 p hg
    simpa only [d95, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8247 (p : Pattern) (guard : d1294 p = 1) : d720 p ≤ (0 : Int) + d96 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d720, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8198 p hg
    simpa only [d720, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d720, d96, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8246 p hg
    simpa only [d720, d96, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8248 (p : Pattern) (guard : d1293 p = 1) : d705 p ≤ (0 : Int) + d97 p := by
  cases selected : p 139 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d705, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8175 p hg
    simpa only [d705, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d705, d97, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4473 p hg
    simpa only [d705, d97, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8249 (p : Pattern) (guard : d1293 p = 1) : d706 p ≤ (0 : Int) + d98 p := by
  cases selected : p 138 with
  | false =>
    have hg : d1293 p = 1 := by simpa only [d706, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8175 p hg
    simpa only [d706, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d706, d98, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8248 p hg
    simpa only [d706, d98, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8250 (p : Pattern) (guard : d1294 p = 1) : d706 p ≤ (0 : Int) + d98 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7747 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8249 p hg
    simpa only [d1294, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8251 (p : Pattern) (guard : d1294 p = 1) : d706 p ≤ (0 : Int) + d99 p := by
  cases selected : p 134 with
  | false =>
    have hg : d917 p = 1 := by simpa only [d1294, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare7747 p hg
    simpa only [d1294, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1293 p = 1 := by simpa only [d1294, d99, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8222 p hg
    simpa only [d1294, d99, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8252 (p : Pattern) (guard : d1294 p = 1) : d706 p ≤ (0 : Int) + d100 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8250 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8251 p hg
    simpa only [d100, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8253 (p : Pattern) (guard : d1294 p = 1) : d706 p ≤ (0 : Int) + d101 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8251 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8223 p hg
    simpa only [d101, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8254 (p : Pattern) (guard : d1294 p = 1) : d706 p ≤ (0 : Int) + d102 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8252 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8253 p hg
    simpa only [d102, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8255 (p : Pattern) (guard : d1294 p = 1) : d721 p ≤ (0 : Int) + d103 p := by
  cases selected : p 112 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d721, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8247 p hg
    simpa only [d721, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d721, d103, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8254 p hg
    simpa only [d721, d103, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8256 (p : Pattern) (guard : d1294 p = 1) : d722 p ≤ (0 : Int) + d104 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d722, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8240 p hg
    simpa only [d722, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d722, d104, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8226 p hg
    simpa only [d722, d104, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8257 (p : Pattern) (guard : d1294 p = 1) : d723 p ≤ (0 : Int) + d105 p := by
  cases selected : p 132 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d723, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8241 p hg
    simpa only [d723, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d723, d105, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8256 p hg
    simpa only [d723, d105, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8258 (p : Pattern) (guard : d1294 p = 1) : d724 p ≤ (0 : Int) + d106 p := by
  cases selected : p 113 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d724, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8228 p hg
    simpa only [d724, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d724, d106, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8257 p hg
    simpa only [d724, d106, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare8259 (p : Pattern) (guard : d1294 p = 1) : d725 p ≤ (0 : Int) + d107 p := by
  cases selected : p 133 with
  | false =>
    have hg : d1294 p = 1 := by simpa only [d725, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare8251 p hg
    simpa only [d725, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1294 p = 1 := by simpa only [d725, d107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4572 p hg
    simpa only [d725, d107, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban32Refined
