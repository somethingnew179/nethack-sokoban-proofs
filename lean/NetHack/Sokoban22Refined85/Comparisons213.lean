/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons212
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare29820 (p : Pattern) (guard : d5843 p = 1) : d3556 p ≤ (0 : Int) + d2011 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3556, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29235 p hg
    simpa only [d3556, d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3556, d2011, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29240 p hg
    simpa only [d3556, d2011, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29821 (p : Pattern) (guard : d5843 p = 1) : d3557 p ≤ (0 : Int) + d2012 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3557, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29820 p hg
    simpa only [d3557, d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3557, d2012, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29240 p hg
    simpa only [d3557, d2012, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29822 (p : Pattern) (guard : d5843 p = 1) : d3558 p ≤ (0 : Int) + d2897 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3558, d2897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29235 p hg
    simpa only [d3558, d2897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3558, d2897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29821 p hg
    simpa only [d3558, d2897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29823 (p : Pattern) (guard : d5843 p = 1) : d3560 p ≤ (0 : Int) + d1695 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3560, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29235 p hg
    simpa only [d3560, d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3560, d1695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29247 p hg
    simpa only [d3560, d1695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29824 (p : Pattern) (guard : d5843 p = 1) : d3561 p ≤ (0 : Int) + d1696 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3561, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29823 p hg
    simpa only [d3561, d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3561, d1696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29247 p hg
    simpa only [d3561, d1696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29825 (p : Pattern) (guard : d5843 p = 1) : d3562 p ≤ (0 : Int) + d1697 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3562, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29824 p hg
    simpa only [d3562, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3562, d1697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3562, d1697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29826 (p : Pattern) (guard : d5843 p = 1) : d3563 p ≤ (0 : Int) + d2898 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3563, d2898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29822 p hg
    simpa only [d3563, d2898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3563, d2898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29825 p hg
    simpa only [d3563, d2898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29827 (p : Pattern) (guard : d5843 p = 1) : d3564 p ≤ (0 : Int) + d2899 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3564, d2899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29818 p hg
    simpa only [d3564, d2899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3564, d2899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29826 p hg
    simpa only [d3564, d2899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29828 (p : Pattern) (guard : d5843 p = 1) : d3565 p ≤ (0 : Int) + d2900 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3565, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29819 p hg
    simpa only [d3565, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3565, d2900, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29827 p hg
    simpa only [d3565, d2900, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29829 (p : Pattern) (guard : d5843 p = 1) : d3566 p ≤ (0 : Int) + d1802 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3566, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29254 p hg
    simpa only [d3566, d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3566, d1802, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20552 p hg
    simpa only [d3566, d1802, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29830 (p : Pattern) (guard : d5843 p = 1) : d3567 p ≤ (0 : Int) + d1803 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3567, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29829 p hg
    simpa only [d3567, d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3567, d1803, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20552 p hg
    simpa only [d3567, d1803, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29831 (p : Pattern) (guard : d5843 p = 1) : d3568 p ≤ (0 : Int) + d2901 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3568, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29254 p hg
    simpa only [d3568, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3568, d2901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29830 p hg
    simpa only [d3568, d2901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29832 (p : Pattern) (guard : d5843 p = 1) : d3570 p ≤ (0 : Int) + d1703 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3570, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29254 p hg
    simpa only [d3570, d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3570, d1703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29263 p hg
    simpa only [d3570, d1703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29833 (p : Pattern) (guard : d5843 p = 1) : d3571 p ≤ (0 : Int) + d1704 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3571, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29832 p hg
    simpa only [d3571, d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3571, d1704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29263 p hg
    simpa only [d3571, d1704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29834 (p : Pattern) (guard : d5843 p = 1) : d3572 p ≤ (0 : Int) + d1705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3572, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29833 p hg
    simpa only [d3572, d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3572, d1705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3572, d1705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29835 (p : Pattern) (guard : d5843 p = 1) : d3573 p ≤ (0 : Int) + d2902 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3573, d2902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29831 p hg
    simpa only [d3573, d2902, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3573, d2902, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29834 p hg
    simpa only [d3573, d2902, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29836 (p : Pattern) (guard : d5843 p = 1) : d3574 p ≤ (0 : Int) + d2903 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3574, d2903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29835 p hg
    simpa only [d3574, d2903, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3574, d2903, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3574, d2903, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29837 (p : Pattern) (guard : d5843 p = 1) : d3575 p ≤ (0 : Int) + d2904 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3575, d2904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29827 p hg
    simpa only [d3575, d2904, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3575, d2904, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29836 p hg
    simpa only [d3575, d2904, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29838 (p : Pattern) (guard : d5843 p = 1) : d3576 p ≤ (0 : Int) + d2905 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3576, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29828 p hg
    simpa only [d3576, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3576, d2905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29837 p hg
    simpa only [d3576, d2905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29839 (p : Pattern) (guard : d5843 p = 1) : d13 p ≤ (0 : Int) + d1775 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d13, d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d13, d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d13, d1775, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare26360 p hg
    simpa only [d5843, d13, d1775, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29840 (p : Pattern) (guard : d5843 p = 1) : d3577 p ≤ (0 : Int) + d1776 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3577, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29839 p hg
    simpa only [d3577, d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3577, d1776, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19928 p hg
    simpa only [d3577, d1776, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29841 (p : Pattern) (guard : d5843 p = 1) : d3578 p ≤ (0 : Int) + d1777 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3578, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d3578, d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3578, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29840 p hg
    simpa only [d3578, d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29842 (p : Pattern) (guard : d5843 p = 1) : d13 p ≤ (0 : Int) + d1785 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d13, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d13, d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d13, d1785, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23451 p hg
    simpa only [d5843, d13, d1785, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29843 (p : Pattern) (guard : d5843 p = 1) : d3579 p ≤ (0 : Int) + d1786 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3579, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29842 p hg
    simpa only [d3579, d1786, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3579, d1786, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19889 p hg
    simpa only [d3579, d1786, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29844 (p : Pattern) (guard : d5843 p = 1) : d3580 p ≤ (0 : Int) + d1787 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3580, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29215 p hg
    simpa only [d3580, d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3580, d1787, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29843 p hg
    simpa only [d3580, d1787, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29845 (p : Pattern) (guard : d5843 p = 1) : d3581 p ≤ (0 : Int) + d1788 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3581, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29841 p hg
    simpa only [d3581, d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3581, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29844 p hg
    simpa only [d3581, d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29846 (p : Pattern) (guard : d5843 p = 1) : d3582 p ≤ (0 : Int) + d2906 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3582, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d3582, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3582, d2906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29845 p hg
    simpa only [d3582, d2906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29847 (p : Pattern) (guard : d5843 p = 1) : d30 p ≤ (0 : Int) + d1710 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d30, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14558 p hg
    simpa only [d5843, d30, d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d30, d1710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23784 p hg
    simpa only [d5843, d30, d1710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29848 (p : Pattern) (guard : d5843 p = 1) : d3583 p ≤ (0 : Int) + d1711 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3583, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29847 p hg
    simpa only [d3583, d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3583, d1711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20378 p hg
    simpa only [d3583, d1711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29849 (p : Pattern) (guard : d5843 p = 1) : d3584 p ≤ (0 : Int) + d1712 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3584, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29277 p hg
    simpa only [d3584, d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3584, d1712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29848 p hg
    simpa only [d3584, d1712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29850 (p : Pattern) (guard : d5843 p = 1) : d3586 p ≤ (0 : Int) + d1716 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3586, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29281 p hg
    simpa only [d3586, d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3586, d1716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25864 p hg
    simpa only [d3586, d1716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29851 (p : Pattern) (guard : d5843 p = 1) : d3587 p ≤ (0 : Int) + d1717 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3587, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29849 p hg
    simpa only [d3587, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3587, d1717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29850 p hg
    simpa only [d3587, d1717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29852 (p : Pattern) (guard : d5843 p = 1) : d3588 p ≤ (0 : Int) + d1718 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3588, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29851 p hg
    simpa only [d3588, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3588, d1718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3588, d1718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29853 (p : Pattern) (guard : d5843 p = 1) : d3589 p ≤ (0 : Int) + d2907 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3589, d2907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29846 p hg
    simpa only [d3589, d2907, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3589, d2907, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29852 p hg
    simpa only [d3589, d2907, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29854 (p : Pattern) (guard : d5843 p = 1) : d3590 p ≤ (0 : Int) + d1720 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3590, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29286 p hg
    simpa only [d3590, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3590, d1720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25869 p hg
    simpa only [d3590, d1720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29855 (p : Pattern) (guard : d5843 p = 1) : d3592 p ≤ (0 : Int) + d1723 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3592, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29289 p hg
    simpa only [d3592, d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3592, d1723, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25869 p hg
    simpa only [d3592, d1723, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29856 (p : Pattern) (guard : d5843 p = 1) : d3593 p ≤ (0 : Int) + d1724 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3593, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29854 p hg
    simpa only [d3593, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3593, d1724, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29855 p hg
    simpa only [d3593, d1724, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29857 (p : Pattern) (guard : d5843 p = 1) : d3594 p ≤ (0 : Int) + d1725 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3594, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29856 p hg
    simpa only [d3594, d1725, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3594, d1725, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3594, d1725, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29858 (p : Pattern) (guard : d5843 p = 1) : d3595 p ≤ (0 : Int) + d2908 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3595, d2908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29846 p hg
    simpa only [d3595, d2908, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3595, d2908, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29857 p hg
    simpa only [d3595, d2908, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29859 (p : Pattern) (guard : d5843 p = 1) : d3596 p ≤ (0 : Int) + d2909 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3596, d2909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29853 p hg
    simpa only [d3596, d2909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3596, d2909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29858 p hg
    simpa only [d3596, d2909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29860 (p : Pattern) (guard : d5843 p = 1) : d3597 p ≤ (0 : Int) + d1728 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3597, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29295 p hg
    simpa only [d3597, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3597, d1728, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20591 p hg
    simpa only [d3597, d1728, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29861 (p : Pattern) (guard : d5843 p = 1) : d3598 p ≤ (0 : Int) + d1729 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3598, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29860 p hg
    simpa only [d3598, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3598, d1729, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20591 p hg
    simpa only [d3598, d1729, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29862 (p : Pattern) (guard : d5843 p = 1) : d3599 p ≤ (0 : Int) + d1730 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3599, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29861 p hg
    simpa only [d3599, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3599, d1730, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3599, d1730, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29863 (p : Pattern) (guard : d5843 p = 1) : d3600 p ≤ (0 : Int) + d2910 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3600, d2910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29846 p hg
    simpa only [d3600, d2910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3600, d2910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29862 p hg
    simpa only [d3600, d2910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29864 (p : Pattern) (guard : d5843 p = 1) : d17 p ≤ (0 : Int) + d1791 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d17, d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14537 p hg
    simpa only [d5843, d17, d1791, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d17, d1791, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23493 p hg
    simpa only [d5843, d17, d1791, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29865 (p : Pattern) (guard : d5843 p = 1) : d3601 p ≤ (0 : Int) + d1792 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3601, d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29864 p hg
    simpa only [d3601, d1792, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3601, d1792, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19992 p hg
    simpa only [d3601, d1792, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29866 (p : Pattern) (guard : d5843 p = 1) : d3602 p ≤ (0 : Int) + d1793 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3602, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29235 p hg
    simpa only [d3602, d1793, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3602, d1793, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29865 p hg
    simpa only [d3602, d1793, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29867 (p : Pattern) (guard : d5843 p = 1) : d3603 p ≤ (0 : Int) + d1796 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3603, d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29240 p hg
    simpa only [d3603, d1796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3603, d1796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25883 p hg
    simpa only [d3603, d1796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29868 (p : Pattern) (guard : d5843 p = 1) : d3604 p ≤ (0 : Int) + d1797 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3604, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29866 p hg
    simpa only [d3604, d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3604, d1797, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29867 p hg
    simpa only [d3604, d1797, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29869 (p : Pattern) (guard : d5843 p = 1) : d3605 p ≤ (0 : Int) + d2911 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3605, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29235 p hg
    simpa only [d3605, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3605, d2911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29868 p hg
    simpa only [d3605, d2911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29870 (p : Pattern) (guard : d5843 p = 1) : d3606 p ≤ (0 : Int) + d2912 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3606, d2912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29869 p hg
    simpa only [d3606, d2912, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3606, d2912, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3606, d2912, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29871 (p : Pattern) (guard : d5843 p = 1) : d3607 p ≤ (0 : Int) + d2913 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3607, d2913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29863 p hg
    simpa only [d3607, d2913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3607, d2913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29870 p hg
    simpa only [d3607, d2913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29872 (p : Pattern) (guard : d5843 p = 1) : d3608 p ≤ (0 : Int) + d2914 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3608, d2914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29859 p hg
    simpa only [d3608, d2914, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3608, d2914, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29871 p hg
    simpa only [d3608, d2914, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29873 (p : Pattern) (guard : d5843 p = 1) : d3609 p ≤ (0 : Int) + d2915 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3609, d2915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29846 p hg
    simpa only [d3609, d2915, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3609, d2915, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3609, d2915, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29874 (p : Pattern) (guard : d5843 p = 1) : d3610 p ≤ (0 : Int) + d2916 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3610, d2916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29873 p hg
    simpa only [d3610, d2916, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3610, d2916, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29870 p hg
    simpa only [d3610, d2916, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29875 (p : Pattern) (guard : d5843 p = 1) : d3611 p ≤ (0 : Int) + d2917 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3611, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29831 p hg
    simpa only [d3611, d2917, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3611, d2917, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3611, d2917, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29876 (p : Pattern) (guard : d5843 p = 1) : d3612 p ≤ (0 : Int) + d2918 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3612, d2918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29875 p hg
    simpa only [d3612, d2918, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3612, d2918, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3612, d2918, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29877 (p : Pattern) (guard : d5843 p = 1) : d3613 p ≤ (0 : Int) + d2919 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3613, d2919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29874 p hg
    simpa only [d3613, d2919, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3613, d2919, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29876 p hg
    simpa only [d3613, d2919, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29878 (p : Pattern) (guard : d5843 p = 1) : d3614 p ≤ (0 : Int) + d2920 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3614, d2920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29872 p hg
    simpa only [d3614, d2920, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3614, d2920, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29877 p hg
    simpa only [d3614, d2920, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29879 (p : Pattern) (guard : d5843 p = 1) : d3615 p ≤ (0 : Int) + d2921 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3615, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29838 p hg
    simpa only [d3615, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3615, d2921, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29878 p hg
    simpa only [d3615, d2921, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29880 (p : Pattern) (guard : d5843 p = 1) : d3617 p ≤ (0 : Int) + d14 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29318 p hg
    simpa only [d3617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d3617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29881 (p : Pattern) (guard : d5843 p = 1) : d3618 p ≤ (0 : Int) + d14 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29880 p hg
    simpa only [d3618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d3618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29882 (p : Pattern) (guard : d5843 p = 1) : d3619 p ≤ (0 : Int) + d2895 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3619, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29881 p hg
    simpa only [d3619, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3619, d2895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29811 p hg
    simpa only [d3619, d2895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29883 (p : Pattern) (guard : d5843 p = 1) : d3620 p ≤ (0 : Int) + d2896 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3620, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29882 p hg
    simpa only [d3620, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3620, d2896, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29815 p hg
    simpa only [d3620, d2896, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29884 (p : Pattern) (guard : d5843 p = 1) : d3621 p ≤ (0 : Int) + d2029 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3621, d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29277 p hg
    simpa only [d3621, d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3621, d2029, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29281 p hg
    simpa only [d3621, d2029, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29885 (p : Pattern) (guard : d5843 p = 1) : d3622 p ≤ (0 : Int) + d2030 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3622, d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29884 p hg
    simpa only [d3622, d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3622, d2030, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29281 p hg
    simpa only [d3622, d2030, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29886 (p : Pattern) (guard : d5843 p = 1) : d3623 p ≤ (0 : Int) + d2922 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3623, d2922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29277 p hg
    simpa only [d3623, d2922, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3623, d2922, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29885 p hg
    simpa only [d3623, d2922, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29887 (p : Pattern) (guard : d5843 p = 1) : d3625 p ≤ (0 : Int) + d1744 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3625, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29277 p hg
    simpa only [d3625, d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3625, d1744, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29333 p hg
    simpa only [d3625, d1744, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29888 (p : Pattern) (guard : d5843 p = 1) : d3626 p ≤ (0 : Int) + d1745 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3626, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29887 p hg
    simpa only [d3626, d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3626, d1745, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29333 p hg
    simpa only [d3626, d1745, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29889 (p : Pattern) (guard : d5843 p = 1) : d3627 p ≤ (0 : Int) + d1746 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3627, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29888 p hg
    simpa only [d3627, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3627, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3627, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29890 (p : Pattern) (guard : d5843 p = 1) : d3628 p ≤ (0 : Int) + d2923 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3628, d2923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29886 p hg
    simpa only [d3628, d2923, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3628, d2923, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29889 p hg
    simpa only [d3628, d2923, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29891 (p : Pattern) (guard : d5843 p = 1) : d3629 p ≤ (0 : Int) + d2924 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3629, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29883 p hg
    simpa only [d3629, d2924, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3629, d2924, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29890 p hg
    simpa only [d3629, d2924, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29892 (p : Pattern) (guard : d5843 p = 1) : d3630 p ≤ (0 : Int) + d2925 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3630, d2925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29826 p hg
    simpa only [d3630, d2925, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3630, d2925, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29835 p hg
    simpa only [d3630, d2925, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29893 (p : Pattern) (guard : d5843 p = 1) : d3631 p ≤ (0 : Int) + d2926 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3631, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29891 p hg
    simpa only [d3631, d2926, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3631, d2926, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29892 p hg
    simpa only [d3631, d2926, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29894 (p : Pattern) (guard : d5843 p = 1) : d3632 p ≤ (0 : Int) + d1751 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3632, d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29341 p hg
    simpa only [d3632, d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3632, d1751, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20634 p hg
    simpa only [d3632, d1751, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29895 (p : Pattern) (guard : d5843 p = 1) : d3633 p ≤ (0 : Int) + d1752 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3633, d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29894 p hg
    simpa only [d3633, d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3633, d1752, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20634 p hg
    simpa only [d3633, d1752, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29896 (p : Pattern) (guard : d5843 p = 1) : d3634 p ≤ (0 : Int) + d2927 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3634, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29341 p hg
    simpa only [d3634, d2927, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3634, d2927, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29895 p hg
    simpa only [d3634, d2927, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29897 (p : Pattern) (guard : d5843 p = 1) : d3635 p ≤ (0 : Int) + d1753 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3635, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29895 p hg
    simpa only [d3635, d1753, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3635, d1753, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3635, d1753, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29898 (p : Pattern) (guard : d5843 p = 1) : d3636 p ≤ (0 : Int) + d2928 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3636, d2928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29896 p hg
    simpa only [d3636, d2928, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3636, d2928, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29897 p hg
    simpa only [d3636, d2928, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29899 (p : Pattern) (guard : d5843 p = 1) : d3637 p ≤ (0 : Int) + d2929 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3637, d2929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29826 p hg
    simpa only [d3637, d2929, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3637, d2929, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29898 p hg
    simpa only [d3637, d2929, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29900 (p : Pattern) (guard : d5843 p = 1) : d3638 p ≤ (0 : Int) + d2930 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3638, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29295 p hg
    simpa only [d3638, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3638, d2930, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29861 p hg
    simpa only [d3638, d2930, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29901 (p : Pattern) (guard : d5843 p = 1) : d3639 p ≤ (0 : Int) + d2931 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3639, d2931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29900 p hg
    simpa only [d3639, d2931, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3639, d2931, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29862 p hg
    simpa only [d3639, d2931, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29902 (p : Pattern) (guard : d5843 p = 1) : d3640 p ≤ (0 : Int) + d2932 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3640, d2932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29901 p hg
    simpa only [d3640, d2932, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3640, d2932, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3640, d2932, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29903 (p : Pattern) (guard : d5843 p = 1) : d3641 p ≤ (0 : Int) + d2933 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3641, d2933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29899 p hg
    simpa only [d3641, d2933, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3641, d2933, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29902 p hg
    simpa only [d3641, d2933, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29904 (p : Pattern) (guard : d5843 p = 1) : d3642 p ≤ (0 : Int) + d2934 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3642, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29893 p hg
    simpa only [d3642, d2934, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3642, d2934, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29903 p hg
    simpa only [d3642, d2934, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29905 (p : Pattern) (guard : d5843 p = 1) : d3643 p ≤ (0 : Int) + d2935 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3643, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29277 p hg
    simpa only [d3643, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3643, d2935, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29851 p hg
    simpa only [d3643, d2935, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29906 (p : Pattern) (guard : d5843 p = 1) : d3644 p ≤ (0 : Int) + d2936 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3644, d2936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29905 p hg
    simpa only [d3644, d2936, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3644, d2936, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3644, d2936, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29907 (p : Pattern) (guard : d5843 p = 1) : d3645 p ≤ (0 : Int) + d2937 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3645, d2937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29858 p hg
    simpa only [d3645, d2937, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3645, d2937, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29906 p hg
    simpa only [d3645, d2937, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29908 (p : Pattern) (guard : d5843 p = 1) : d3646 p ≤ (0 : Int) + d2938 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3646, d2938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29870 p hg
    simpa only [d3646, d2938, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3646, d2938, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29875 p hg
    simpa only [d3646, d2938, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29909 (p : Pattern) (guard : d5843 p = 1) : d3647 p ≤ (0 : Int) + d2939 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3647, d2939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29907 p hg
    simpa only [d3647, d2939, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3647, d2939, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29908 p hg
    simpa only [d3647, d2939, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29910 (p : Pattern) (guard : d5843 p = 1) : d3648 p ≤ (0 : Int) + d2940 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3648, d2940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29896 p hg
    simpa only [d3648, d2940, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3648, d2940, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3648, d2940, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29911 (p : Pattern) (guard : d5843 p = 1) : d3649 p ≤ (0 : Int) + d2941 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3649, d2941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29870 p hg
    simpa only [d3649, d2941, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3649, d2941, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29910 p hg
    simpa only [d3649, d2941, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29912 (p : Pattern) (guard : d5843 p = 1) : d3650 p ≤ (0 : Int) + d2942 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3650, d2942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29900 p hg
    simpa only [d3650, d2942, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3650, d2942, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3650, d2942, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29913 (p : Pattern) (guard : d5843 p = 1) : d3651 p ≤ (0 : Int) + d2943 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3651, d2943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29912 p hg
    simpa only [d3651, d2943, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3651, d2943, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3651, d2943, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29914 (p : Pattern) (guard : d5843 p = 1) : d3652 p ≤ (0 : Int) + d2944 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3652, d2944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29911 p hg
    simpa only [d3652, d2944, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3652, d2944, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29913 p hg
    simpa only [d3652, d2944, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29915 (p : Pattern) (guard : d5843 p = 1) : d3653 p ≤ (0 : Int) + d2945 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3653, d2945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29909 p hg
    simpa only [d3653, d2945, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3653, d2945, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29914 p hg
    simpa only [d3653, d2945, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29916 (p : Pattern) (guard : d5843 p = 1) : d3654 p ≤ (0 : Int) + d2946 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3654, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29904 p hg
    simpa only [d3654, d2946, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3654, d2946, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29915 p hg
    simpa only [d3654, d2946, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29917 (p : Pattern) (guard : d5843 p = 1) : d3655 p ≤ (0 : Int) + d2947 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3655, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29879 p hg
    simpa only [d3655, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3655, d2947, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29916 p hg
    simpa only [d3655, d2947, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29918 (p : Pattern) (guard : d5843 p = 1) : d3656 p ≤ (0 : Int) + d2047 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3656, d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29215 p hg
    simpa only [d3656, d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3656, d2047, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29840 p hg
    simpa only [d3656, d2047, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29919 (p : Pattern) (guard : d5843 p = 1) : d3657 p ≤ (0 : Int) + d2048 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3657, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29841 p hg
    simpa only [d3657, d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3657, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29918 p hg
    simpa only [d3657, d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29920 (p : Pattern) (guard : d5843 p = 1) : d3658 p ≤ (0 : Int) + d2948 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3658, d2948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d3658, d2948, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3658, d2948, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29919 p hg
    simpa only [d3658, d2948, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29921 (p : Pattern) (guard : d5843 p = 1) : d3659 p ≤ (0 : Int) + d1773 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3659, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29811 p hg
    simpa only [d3659, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3659, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3659, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29922 (p : Pattern) (guard : d5843 p = 1) : d3660 p ≤ (0 : Int) + d2949 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3660, d2949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29920 p hg
    simpa only [d3660, d2949, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3660, d2949, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29921 p hg
    simpa only [d3660, d2949, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29923 (p : Pattern) (guard : d5843 p = 1) : d13 p ≤ (0 : Int) + d2051 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d13, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d13, d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d13, d2051, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23493 p hg
    simpa only [d5843, d13, d2051, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29924 (p : Pattern) (guard : d5843 p = 1) : d3579 p ≤ (0 : Int) + d2052 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3579, d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29923 p hg
    simpa only [d3579, d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3579, d2052, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19889 p hg
    simpa only [d3579, d2052, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29925 (p : Pattern) (guard : d5843 p = 1) : d3580 p ≤ (0 : Int) + d2053 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3580, d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29215 p hg
    simpa only [d3580, d2053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3580, d2053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29924 p hg
    simpa only [d3580, d2053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29926 (p : Pattern) (guard : d5843 p = 1) : d3581 p ≤ (0 : Int) + d2054 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3581, d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29841 p hg
    simpa only [d3581, d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3581, d2054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29925 p hg
    simpa only [d3581, d2054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29927 (p : Pattern) (guard : d5843 p = 1) : d3582 p ≤ (0 : Int) + d2950 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3582, d2950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29209 p hg
    simpa only [d3582, d2950, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3582, d2950, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29926 p hg
    simpa only [d3582, d2950, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29928 (p : Pattern) (guard : d5843 p = 1) : d13 p ≤ (0 : Int) + d1778 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d13, d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1086 p hg
    simpa only [d5843, d13, d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d13, d1778, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare23784 p hg
    simpa only [d5843, d13, d1778, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29929 (p : Pattern) (guard : d5843 p = 1) : d3661 p ≤ (0 : Int) + d1779 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3661, d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29928 p hg
    simpa only [d3661, d1779, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3661, d1779, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20378 p hg
    simpa only [d3661, d1779, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29930 (p : Pattern) (guard : d5843 p = 1) : d3662 p ≤ (0 : Int) + d1780 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3662, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29215 p hg
    simpa only [d3662, d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3662, d1780, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29929 p hg
    simpa only [d3662, d1780, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29931 (p : Pattern) (guard : d5843 p = 1) : d3663 p ≤ (0 : Int) + d1781 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3663, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29841 p hg
    simpa only [d3663, d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3663, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29930 p hg
    simpa only [d3663, d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29932 (p : Pattern) (guard : d5843 p = 1) : d3664 p ≤ (0 : Int) + d1782 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3664, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29931 p hg
    simpa only [d3664, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3664, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3664, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29933 (p : Pattern) (guard : d5843 p = 1) : d3665 p ≤ (0 : Int) + d2951 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3665, d2951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29927 p hg
    simpa only [d3665, d2951, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3665, d2951, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29932 p hg
    simpa only [d3665, d2951, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29934 (p : Pattern) (guard : d5843 p = 1) : d3666 p ≤ (0 : Int) + d2952 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3666, d2952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29922 p hg
    simpa only [d3666, d2952, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3666, d2952, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29933 p hg
    simpa only [d3666, d2952, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29935 (p : Pattern) (guard : d5843 p = 1) : d3667 p ≤ (0 : Int) + d1789 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3667, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29845 p hg
    simpa only [d3667, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3667, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3667, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29936 (p : Pattern) (guard : d5843 p = 1) : d3668 p ≤ (0 : Int) + d2953 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3668, d2953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29846 p hg
    simpa only [d3668, d2953, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3668, d2953, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29935 p hg
    simpa only [d3668, d2953, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29937 (p : Pattern) (guard : d5843 p = 1) : d3669 p ≤ (0 : Int) + d1798 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3669, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29868 p hg
    simpa only [d3669, d1798, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3669, d1798, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3669, d1798, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29938 (p : Pattern) (guard : d5843 p = 1) : d3670 p ≤ (0 : Int) + d2954 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3670, d2954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29869 p hg
    simpa only [d3670, d2954, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3670, d2954, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29937 p hg
    simpa only [d3670, d2954, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29939 (p : Pattern) (guard : d5843 p = 1) : d3671 p ≤ (0 : Int) + d2955 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3671, d2955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29936 p hg
    simpa only [d3671, d2955, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3671, d2955, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29938 p hg
    simpa only [d3671, d2955, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29940 (p : Pattern) (guard : d5843 p = 1) : d3672 p ≤ (0 : Int) + d2956 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3672, d2956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29934 p hg
    simpa only [d3672, d2956, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3672, d2956, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29939 p hg
    simpa only [d3672, d2956, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29941 (p : Pattern) (guard : d5843 p = 1) : d3673 p ≤ (0 : Int) + d1804 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3673, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29830 p hg
    simpa only [d3673, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3673, d1804, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3673, d1804, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29942 (p : Pattern) (guard : d5843 p = 1) : d3674 p ≤ (0 : Int) + d2957 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3674, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29831 p hg
    simpa only [d3674, d2957, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3674, d2957, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29941 p hg
    simpa only [d3674, d2957, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29943 (p : Pattern) (guard : d5843 p = 1) : d3675 p ≤ (0 : Int) + d2958 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3675, d2958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29942 p hg
    simpa only [d3675, d2958, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3675, d2958, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3675, d2958, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29944 (p : Pattern) (guard : d5843 p = 1) : d3676 p ≤ (0 : Int) + d2959 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3676, d2959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29939 p hg
    simpa only [d3676, d2959, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3676, d2959, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29943 p hg
    simpa only [d3676, d2959, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29945 (p : Pattern) (guard : d5843 p = 1) : d3677 p ≤ (0 : Int) + d2960 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3677, d2960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29940 p hg
    simpa only [d3677, d2960, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3677, d2960, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29944 p hg
    simpa only [d3677, d2960, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29946 (p : Pattern) (guard : d5843 p = 1) : d3678 p ≤ (0 : Int) + d2961 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3678, d2961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29905 p hg
    simpa only [d3678, d2961, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3678, d2961, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29852 p hg
    simpa only [d3678, d2961, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29947 (p : Pattern) (guard : d5843 p = 1) : d3679 p ≤ (0 : Int) + d2962 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3679, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29286 p hg
    simpa only [d3679, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3679, d2962, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29856 p hg
    simpa only [d3679, d2962, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29948 (p : Pattern) (guard : d5843 p = 1) : d3680 p ≤ (0 : Int) + d2963 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3680, d2963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29947 p hg
    simpa only [d3680, d2963, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3680, d2963, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29857 p hg
    simpa only [d3680, d2963, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29949 (p : Pattern) (guard : d5843 p = 1) : d3681 p ≤ (0 : Int) + d2964 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3681, d2964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29946 p hg
    simpa only [d3681, d2964, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3681, d2964, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29948 p hg
    simpa only [d3681, d2964, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29950 (p : Pattern) (guard : d5843 p = 1) : d3682 p ≤ (0 : Int) + d2965 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3682, d2965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29949 p hg
    simpa only [d3682, d2965, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3682, d2965, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29902 p hg
    simpa only [d3682, d2965, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29951 (p : Pattern) (guard : d5843 p = 1) : d3683 p ≤ (0 : Int) + d2966 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3683, d2966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29950 p hg
    simpa only [d3683, d2966, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3683, d2966, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3683, d2966, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29952 (p : Pattern) (guard : d5843 p = 1) : d3684 p ≤ (0 : Int) + d2967 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3684, d2967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29945 p hg
    simpa only [d3684, d2967, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3684, d2967, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29951 p hg
    simpa only [d3684, d2967, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29953 (p : Pattern) (guard : d5843 p = 1) : d3685 p ≤ (0 : Int) + d2968 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3685, d2968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29933 p hg
    simpa only [d3685, d2968, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3685, d2968, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29946 p hg
    simpa only [d3685, d2968, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29954 (p : Pattern) (guard : d5843 p = 1) : d3686 p ≤ (0 : Int) + d2969 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3686, d2969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29938 p hg
    simpa only [d3686, d2969, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3686, d2969, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29942 p hg
    simpa only [d3686, d2969, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29955 (p : Pattern) (guard : d5843 p = 1) : d3687 p ≤ (0 : Int) + d2970 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3687, d2970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29953 p hg
    simpa only [d3687, d2970, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3687, d2970, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29954 p hg
    simpa only [d3687, d2970, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29956 (p : Pattern) (guard : d5843 p = 1) : d3688 p ≤ (0 : Int) + d2971 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3688, d2971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29938 p hg
    simpa only [d3688, d2971, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3688, d2971, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29898 p hg
    simpa only [d3688, d2971, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29957 (p : Pattern) (guard : d5843 p = 1) : d3689 p ≤ (0 : Int) + d2972 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3689, d2972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29956 p hg
    simpa only [d3689, d2972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3689, d2972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29902 p hg
    simpa only [d3689, d2972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29958 (p : Pattern) (guard : d5843 p = 1) : d3690 p ≤ (0 : Int) + d2973 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3690, d2973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29955 p hg
    simpa only [d3690, d2973, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3690, d2973, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29957 p hg
    simpa only [d3690, d2973, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare29959 (p : Pattern) (guard : d5843 p = 1) : d3691 p ≤ (0 : Int) + d2974 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d3691, d2974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare29948 p hg
    simpa only [d3691, d2974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d3691, d2974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare25828 p hg
    simpa only [d3691, d2974, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
