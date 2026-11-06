/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons122
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare17220 (p : Pattern) (guard : d0 p = 1) : d1792 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17221 (p : Pattern) (guard : d5502 p = 1) : d1793 p ≤ (0 : Int) + d2520 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1793, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2003 p hg
    simpa only [d5502, d1793, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1793, d2520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17220 p hg
    simpa only [d5502, d1793, d2520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17222 (p : Pattern) (guard : d1 p = 1) : d1795 p ≤ (0 : Int) + d1795 p := by
  omega
theorem compare17223 (p : Pattern) (guard : d0 p = 1) : d339 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17224 (p : Pattern) (guard : d5502 p = 1) : d1796 p ≤ (0 : Int) + d2521 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1796, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17222 p hg
    simpa only [d5502, d1796, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1796, d2521, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17223 p hg
    simpa only [d5502, d1796, d2521, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17225 (p : Pattern) (guard : d5502 p = 1) : d1797 p ≤ (0 : Int) + d2522 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1797, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17221 p hg
    simpa only [d1797, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1797, d2522, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17224 p hg
    simpa only [d1797, d2522, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17226 (p : Pattern) (guard : d5537 p = 1) : d1798 p ≤ (0 : Int) + d2602 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1798, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17225 p hg
    simpa only [d5537, d1798, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1798, d2602, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1798, d2602, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17227 (p : Pattern) (guard : d5537 p = 1) : d1799 p ≤ (0 : Int) + d2603 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1799, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17100 p hg
    simpa only [d1799, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1799, d2603, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17226 p hg
    simpa only [d1799, d2603, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17228 (p : Pattern) (guard : d5537 p = 1) : d1800 p ≤ (0 : Int) + d2604 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1800, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17219 p hg
    simpa only [d1800, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1800, d2604, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17227 p hg
    simpa only [d1800, d2604, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17229 (p : Pattern) (guard : d5537 p = 1) : d1801 p ≤ (0 : Int) + d2605 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1801, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17214 p hg
    simpa only [d1801, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1801, d2605, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17228 p hg
    simpa only [d1801, d2605, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17230 (p : Pattern) (guard : d0 p = 1) : d356 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17231 (p : Pattern) (guard : d5502 p = 1) : d1802 p ≤ (0 : Int) + d2530 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1802, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2010 p hg
    simpa only [d5502, d1802, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1802, d2530, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17230 p hg
    simpa only [d5502, d1802, d2530, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17232 (p : Pattern) (guard : d1 p = 1) : d356 p ≤ (0 : Int) + d356 p := by
  omega
theorem compare17233 (p : Pattern) (guard : d5502 p = 1) : d356 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17232 p hg
    simpa only [d5502, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17230 p hg
    simpa only [d5502, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17234 (p : Pattern) (guard : d5502 p = 1) : d1803 p ≤ (0 : Int) + d2531 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1803, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17231 p hg
    simpa only [d1803, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1803, d2531, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17233 p hg
    simpa only [d1803, d2531, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17235 (p : Pattern) (guard : d5537 p = 1) : d1804 p ≤ (0 : Int) + d2606 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1804, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17234 p hg
    simpa only [d5537, d1804, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1804, d2606, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1804, d2606, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17236 (p : Pattern) (guard : d5537 p = 1) : d1805 p ≤ (0 : Int) + d2607 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1805, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17111 p hg
    simpa only [d1805, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1805, d2607, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17235 p hg
    simpa only [d1805, d2607, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17237 (p : Pattern) (guard : d5537 p = 1) : d1806 p ≤ (0 : Int) + d2608 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1806, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17236 p hg
    simpa only [d1806, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1806, d2608, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1806, d2608, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17238 (p : Pattern) (guard : d5537 p = 1) : d1807 p ≤ (0 : Int) + d2609 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1807, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17228 p hg
    simpa only [d1807, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1807, d2609, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17237 p hg
    simpa only [d1807, d2609, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17239 (p : Pattern) (guard : d5537 p = 1) : d1808 p ≤ (0 : Int) + d2610 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1808, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17229 p hg
    simpa only [d1808, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1808, d2610, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17238 p hg
    simpa only [d1808, d2610, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17240 (p : Pattern) (guard : d5537 p = 1) : d1809 p ≤ (0 : Int) + d2611 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1809, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17161 p hg
    simpa only [d1809, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1809, d2611, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17129 p hg
    simpa only [d1809, d2611, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17241 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2547 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17242 (p : Pattern) (guard : d5537 p = 1) : d36 p ≤ (0 : Int) + d2612 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d36, d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14883 p hg
    simpa only [d5537, d36, d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d36, d2612, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17241 p hg
    simpa only [d5537, d36, d2612, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17243 (p : Pattern) (guard : d5537 p = 1) : d1810 p ≤ (0 : Int) + d2613 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1810, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17242 p hg
    simpa only [d1810, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1810, d2613, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17136 p hg
    simpa only [d1810, d2613, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17244 (p : Pattern) (guard : d5537 p = 1) : d1811 p ≤ (0 : Int) + d2614 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1811, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17240 p hg
    simpa only [d1811, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1811, d2614, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17243 p hg
    simpa only [d1811, d2614, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17245 (p : Pattern) (guard : d5537 p = 1) : d1812 p ≤ (0 : Int) + d2615 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1812, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17244 p hg
    simpa only [d1812, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1812, d2615, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17185 p hg
    simpa only [d1812, d2615, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17246 (p : Pattern) (guard : d5537 p = 1) : d1813 p ≤ (0 : Int) + d2616 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1813, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17245 p hg
    simpa only [d1813, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1813, d2616, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1813, d2616, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17247 (p : Pattern) (guard : d5537 p = 1) : d1814 p ≤ (0 : Int) + d2617 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1814, d2617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17239 p hg
    simpa only [d1814, d2617, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1814, d2617, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17246 p hg
    simpa only [d1814, d2617, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17248 (p : Pattern) (guard : d5537 p = 1) : d1815 p ≤ (0 : Int) + d2618 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1815, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17213 p hg
    simpa only [d1815, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1815, d2618, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17240 p hg
    simpa only [d1815, d2618, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17249 (p : Pattern) (guard : d5537 p = 1) : d1816 p ≤ (0 : Int) + d2619 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1816, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17227 p hg
    simpa only [d1816, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1816, d2619, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17236 p hg
    simpa only [d1816, d2619, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17250 (p : Pattern) (guard : d5537 p = 1) : d1817 p ≤ (0 : Int) + d2620 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1817, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17248 p hg
    simpa only [d1817, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1817, d2620, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17249 p hg
    simpa only [d1817, d2620, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17251 (p : Pattern) (guard : d5537 p = 1) : d1818 p ≤ (0 : Int) + d2621 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1818, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17227 p hg
    simpa only [d1818, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1818, d2621, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17180 p hg
    simpa only [d1818, d2621, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17252 (p : Pattern) (guard : d5537 p = 1) : d1819 p ≤ (0 : Int) + d2622 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1819, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17251 p hg
    simpa only [d1819, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1819, d2622, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17185 p hg
    simpa only [d1819, d2622, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17253 (p : Pattern) (guard : d5537 p = 1) : d1820 p ≤ (0 : Int) + d2623 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1820, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17250 p hg
    simpa only [d1820, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1820, d2623, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17252 p hg
    simpa only [d1820, d2623, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17254 (p : Pattern) (guard : d5537 p = 1) : d1821 p ≤ (0 : Int) + d2624 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1821, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17243 p hg
    simpa only [d1821, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1821, d2624, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1821, d2624, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17255 (p : Pattern) (guard : d5537 p = 1) : d1822 p ≤ (0 : Int) + d2625 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1822, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17254 p hg
    simpa only [d1822, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1822, d2625, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1822, d2625, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17256 (p : Pattern) (guard : d5537 p = 1) : d1823 p ≤ (0 : Int) + d2626 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1823, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17255 p hg
    simpa only [d1823, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1823, d2626, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1823, d2626, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17257 (p : Pattern) (guard : d5537 p = 1) : d1824 p ≤ (0 : Int) + d2627 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1824, d2627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17253 p hg
    simpa only [d1824, d2627, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1824, d2627, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17256 p hg
    simpa only [d1824, d2627, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17258 (p : Pattern) (guard : d5537 p = 1) : d1825 p ≤ (0 : Int) + d2628 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1825, d2628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17247 p hg
    simpa only [d1825, d2628, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1825, d2628, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17257 p hg
    simpa only [d1825, d2628, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17259 (p : Pattern) (guard : d5537 p = 1) : d1826 p ≤ (0 : Int) + d2629 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1826, d2629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17199 p hg
    simpa only [d1826, d2629, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1826, d2629, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17258 p hg
    simpa only [d1826, d2629, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17260 (p : Pattern) (guard : d5537 p = 1) : d1827 p ≤ (0 : Int) + d2630 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1827, d2630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17236 p hg
    simpa only [d1827, d2630, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1827, d2630, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17184 p hg
    simpa only [d1827, d2630, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17261 (p : Pattern) (guard : d5537 p = 1) : d1828 p ≤ (0 : Int) + d2631 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1828, d2631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17260 p hg
    simpa only [d1828, d2631, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1828, d2631, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17185 p hg
    simpa only [d1828, d2631, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17262 (p : Pattern) (guard : d5537 p = 1) : d1829 p ≤ (0 : Int) + d2632 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1829, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17185 p hg
    simpa only [d1829, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1829, d2632, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1829, d2632, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17263 (p : Pattern) (guard : d5537 p = 1) : d1830 p ≤ (0 : Int) + d2633 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1830, d2633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17261 p hg
    simpa only [d1830, d2633, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1830, d2633, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17262 p hg
    simpa only [d1830, d2633, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17264 (p : Pattern) (guard : d5537 p = 1) : d1831 p ≤ (0 : Int) + d2634 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1831, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17262 p hg
    simpa only [d1831, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1831, d2634, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1831, d2634, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17265 (p : Pattern) (guard : d5537 p = 1) : d1832 p ≤ (0 : Int) + d2635 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1832, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17263 p hg
    simpa only [d1832, d2635, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1832, d2635, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17264 p hg
    simpa only [d1832, d2635, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17266 (p : Pattern) (guard : d5537 p = 1) : d1833 p ≤ (0 : Int) + d2636 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1833, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17264 p hg
    simpa only [d1833, d2636, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1833, d2636, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1833, d2636, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17267 (p : Pattern) (guard : d5537 p = 1) : d1834 p ≤ (0 : Int) + d2637 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1834, d2637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17265 p hg
    simpa only [d1834, d2637, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1834, d2637, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17266 p hg
    simpa only [d1834, d2637, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17268 (p : Pattern) (guard : d5537 p = 1) : d1835 p ≤ (0 : Int) + d2638 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1835, d2638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17258 p hg
    simpa only [d1835, d2638, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1835, d2638, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17267 p hg
    simpa only [d1835, d2638, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17269 (p : Pattern) (guard : d5537 p = 1) : d1836 p ≤ (0 : Int) + d2639 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1836, d2639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17259 p hg
    simpa only [d1836, d2639, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1836, d2639, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17268 p hg
    simpa only [d1836, d2639, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17270 (p : Pattern) (guard : d5537 p = 1) : d1837 p ≤ (0 : Int) + d2640 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1837, d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17094 p hg
    simpa only [d1837, d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1837, d2640, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17098 p hg
    simpa only [d1837, d2640, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17271 (p : Pattern) (guard : d5537 p = 1) : d1838 p ≤ (0 : Int) + d2641 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1838, d2641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17270 p hg
    simpa only [d1838, d2641, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1838, d2641, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17108 p hg
    simpa only [d1838, d2641, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17272 (p : Pattern) (guard : d5537 p = 1) : d1839 p ≤ (0 : Int) + d2642 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1839, d2642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17271 p hg
    simpa only [d1839, d2642, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1839, d2642, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17121 p hg
    simpa only [d1839, d2642, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17273 (p : Pattern) (guard : d5537 p = 1) : d1840 p ≤ (0 : Int) + d2643 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1840, d2643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17272 p hg
    simpa only [d1840, d2643, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1840, d2643, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17154 p hg
    simpa only [d1840, d2643, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17274 (p : Pattern) (guard : d5537 p = 1) : d1841 p ≤ (0 : Int) + d2644 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1841, d2644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17098 p hg
    simpa only [d1841, d2644, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1841, d2644, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17168 p hg
    simpa only [d1841, d2644, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17275 (p : Pattern) (guard : d5537 p = 1) : d1842 p ≤ (0 : Int) + d2645 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1842, d2645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17274 p hg
    simpa only [d1842, d2645, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1842, d2645, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17170 p hg
    simpa only [d1842, d2645, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17276 (p : Pattern) (guard : d5537 p = 1) : d1843 p ≤ (0 : Int) + d2646 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1843, d2646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17275 p hg
    simpa only [d1843, d2646, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1843, d2646, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17186 p hg
    simpa only [d1843, d2646, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17277 (p : Pattern) (guard : d5537 p = 1) : d1844 p ≤ (0 : Int) + d2647 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1844, d2647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17276 p hg
    simpa only [d1844, d2647, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1844, d2647, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17197 p hg
    simpa only [d1844, d2647, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17278 (p : Pattern) (guard : d5537 p = 1) : d1845 p ≤ (0 : Int) + d2648 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1845, d2648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17273 p hg
    simpa only [d1845, d2648, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1845, d2648, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17277 p hg
    simpa only [d1845, d2648, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17279 (p : Pattern) (guard : d5537 p = 1) : d1846 p ≤ (0 : Int) + d2649 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1846, d2649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17278 p hg
    simpa only [d1846, d2649, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1846, d2649, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17258 p hg
    simpa only [d1846, d2649, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17280 (p : Pattern) (guard : d5537 p = 1) : d1847 p ≤ (0 : Int) + d2650 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1847, d2650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17258 p hg
    simpa only [d1847, d2650, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1847, d2650, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1847, d2650, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17281 (p : Pattern) (guard : d5537 p = 1) : d1848 p ≤ (0 : Int) + d2651 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1848, d2651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17279 p hg
    simpa only [d1848, d2651, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1848, d2651, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17280 p hg
    simpa only [d1848, d2651, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17282 (p : Pattern) (guard : d5537 p = 1) : d1849 p ≤ (0 : Int) + d2652 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1849, d2652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17269 p hg
    simpa only [d1849, d2652, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1849, d2652, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17281 p hg
    simpa only [d1849, d2652, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17283 (p : Pattern) (guard : d5502 p = 1) : d14 p ≤ (0 : Int) + d2654 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15003 p hg
    simpa only [d2654, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2654, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare14835 p hg
    simpa only [d2654, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17284 (p : Pattern) (guard : d0 p = 1) : d358 p ≤ (0 : Int) + d2507 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17285 (p : Pattern) (guard : d5537 p = 1) : d1850 p ≤ (0 : Int) + d2655 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1850, d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17283 p hg
    simpa only [d5537, d1850, d2655, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1850, d2655, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17284 p hg
    simpa only [d5537, d1850, d2655, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17286 (p : Pattern) (guard : d5537 p = 1) : d1851 p ≤ (0 : Int) + d2656 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1851, d2656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17285 p hg
    simpa only [d1851, d2656, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1851, d2656, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17089 p hg
    simpa only [d1851, d2656, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17287 (p : Pattern) (guard : d5537 p = 1) : d1852 p ≤ (0 : Int) + d2657 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1852, d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17286 p hg
    simpa only [d1852, d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1852, d2657, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17098 p hg
    simpa only [d1852, d2657, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17288 (p : Pattern) (guard : d5537 p = 1) : d1853 p ≤ (0 : Int) + d2658 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1853, d2658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17287 p hg
    simpa only [d1853, d2658, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1853, d2658, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17108 p hg
    simpa only [d1853, d2658, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17289 (p : Pattern) (guard : d5537 p = 1) : d1854 p ≤ (0 : Int) + d2659 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1854, d2659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17288 p hg
    simpa only [d1854, d2659, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1854, d2659, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17121 p hg
    simpa only [d1854, d2659, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17290 (p : Pattern) (guard : d5537 p = 1) : d1855 p ≤ (0 : Int) + d2660 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1855, d2660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17289 p hg
    simpa only [d1855, d2660, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1855, d2660, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17154 p hg
    simpa only [d1855, d2660, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17291 (p : Pattern) (guard : d5537 p = 1) : d1856 p ≤ (0 : Int) + d2661 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1856, d2661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17094 p hg
    simpa only [d1856, d2661, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1856, d2661, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17168 p hg
    simpa only [d1856, d2661, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17292 (p : Pattern) (guard : d5537 p = 1) : d1857 p ≤ (0 : Int) + d2662 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1857, d2662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17291 p hg
    simpa only [d1857, d2662, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1857, d2662, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17170 p hg
    simpa only [d1857, d2662, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17293 (p : Pattern) (guard : d5537 p = 1) : d1858 p ≤ (0 : Int) + d2663 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1858, d2663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17292 p hg
    simpa only [d1858, d2663, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1858, d2663, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17186 p hg
    simpa only [d1858, d2663, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17294 (p : Pattern) (guard : d5537 p = 1) : d1859 p ≤ (0 : Int) + d2664 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1859, d2664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17293 p hg
    simpa only [d1859, d2664, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1859, d2664, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17197 p hg
    simpa only [d1859, d2664, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17295 (p : Pattern) (guard : d5537 p = 1) : d1860 p ≤ (0 : Int) + d2665 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1860, d2665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17290 p hg
    simpa only [d1860, d2665, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1860, d2665, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17294 p hg
    simpa only [d1860, d2665, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17296 (p : Pattern) (guard : d5537 p = 1) : d1861 p ≤ (0 : Int) + d2666 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1861, d2666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17295 p hg
    simpa only [d1861, d2666, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1861, d2666, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17258 p hg
    simpa only [d1861, d2666, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17297 (p : Pattern) (guard : d5537 p = 1) : d1862 p ≤ (0 : Int) + d2667 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1862, d2667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17296 p hg
    simpa only [d1862, d2667, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1862, d2667, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17268 p hg
    simpa only [d1862, d2667, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17298 (p : Pattern) (guard : d5537 p = 1) : d1863 p ≤ (0 : Int) + d2668 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1863, d2668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17098 p hg
    simpa only [d1863, d2668, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1863, d2668, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17108 p hg
    simpa only [d1863, d2668, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17299 (p : Pattern) (guard : d5537 p = 1) : d1864 p ≤ (0 : Int) + d2669 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1864, d2669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17298 p hg
    simpa only [d1864, d2669, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1864, d2669, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17121 p hg
    simpa only [d1864, d2669, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17300 (p : Pattern) (guard : d5537 p = 1) : d1865 p ≤ (0 : Int) + d2670 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1865, d2670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17299 p hg
    simpa only [d1865, d2670, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1865, d2670, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17154 p hg
    simpa only [d1865, d2670, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17301 (p : Pattern) (guard : d5537 p = 1) : d1866 p ≤ (0 : Int) + d2671 p := by
  cases selected : p 141 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1866, d2671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17300 p hg
    simpa only [d1866, d2671, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1866, d2671, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17277 p hg
    simpa only [d1866, d2671, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17302 (p : Pattern) (guard : d5537 p = 1) : d1867 p ≤ (0 : Int) + d2672 p := by
  cases selected : p 138 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1867, d2672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17301 p hg
    simpa only [d1867, d2672, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1867, d2672, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17258 p hg
    simpa only [d1867, d2672, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17303 (p : Pattern) (guard : d5537 p = 1) : d1868 p ≤ (0 : Int) + d2673 p := by
  cases selected : p 116 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1868, d2673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17302 p hg
    simpa only [d1868, d2673, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1868, d2673, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17280 p hg
    simpa only [d1868, d2673, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17304 (p : Pattern) (guard : d5537 p = 1) : d1869 p ≤ (0 : Int) + d2674 p := by
  cases selected : p 115 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1869, d2674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17297 p hg
    simpa only [d1869, d2674, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1869, d2674, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17303 p hg
    simpa only [d1869, d2674, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17305 (p : Pattern) (guard : d5537 p = 1) : d1870 p ≤ (0 : Int) + d2675 p := by
  cases selected : p 71 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1870, d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17282 p hg
    simpa only [d1870, d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1870, d2675, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17304 p hg
    simpa only [d1870, d2675, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17306 (p : Pattern) (guard : d5502 p = 1) : d103 p ≤ (0 : Int) + d2678 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15027 p hg
    simpa only [d2678, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2678, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15030 p hg
    simpa only [d2678, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17307 (p : Pattern) (guard : d0 p = 1) : d358 p ≤ (0 : Int) + d2680 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17308 (p : Pattern) (guard : d5537 p = 1) : d1871 p ≤ (0 : Int) + d2681 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1871, d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17306 p hg
    simpa only [d5537, d1871, d2681, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1871, d2681, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17307 p hg
    simpa only [d5537, d1871, d2681, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17309 (p : Pattern) (guard : d0 p = 1) : d1873 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17310 (p : Pattern) (guard : d5502 p = 1) : d1874 p ≤ (0 : Int) + d2677 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1874, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1274 p hg
    simpa only [d5502, d1874, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1874, d2677, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17309 p hg
    simpa only [d5502, d1874, d2677, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17311 (p : Pattern) (guard : d1 p = 1) : d1873 p ≤ (0 : Int) + d1873 p := by
  omega
theorem compare17312 (p : Pattern) (guard : d5502 p = 1) : d1873 p ≤ (0 : Int) + d2682 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17311 p hg
    simpa only [d5502, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2682, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17309 p hg
    simpa only [d5502, d2682, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17313 (p : Pattern) (guard : d5502 p = 1) : d1875 p ≤ (0 : Int) + d2683 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1875, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17310 p hg
    simpa only [d1875, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1875, d2683, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17312 p hg
    simpa only [d1875, d2683, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17314 (p : Pattern) (guard : d5537 p = 1) : d1876 p ≤ (0 : Int) + d2684 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1876, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17313 p hg
    simpa only [d5537, d1876, d2684, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1876, d2684, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1876, d2684, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17315 (p : Pattern) (guard : d5537 p = 1) : d1877 p ≤ (0 : Int) + d2685 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1877, d2685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17308 p hg
    simpa only [d1877, d2685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1877, d2685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17314 p hg
    simpa only [d1877, d2685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17316 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2680 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17317 (p : Pattern) (guard : d5537 p = 1) : d104 p ≤ (0 : Int) + d2686 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d104, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15030 p hg
    simpa only [d5537, d104, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d104, d2686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17316 p hg
    simpa only [d5537, d104, d2686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17318 (p : Pattern) (guard : d5537 p = 1) : d1878 p ≤ (0 : Int) + d2687 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1878, d2687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17317 p hg
    simpa only [d1878, d2687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1878, d2687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17314 p hg
    simpa only [d1878, d2687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17319 (p : Pattern) (guard : d5537 p = 1) : d1879 p ≤ (0 : Int) + d2688 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1879, d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17315 p hg
    simpa only [d1879, d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1879, d2688, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17318 p hg
    simpa only [d1879, d2688, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17320 (p : Pattern) (guard : d0 p = 1) : d12 p ≤ (0 : Int) + d2691 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17321 (p : Pattern) (guard : d5537 p = 1) : d108 p ≤ (0 : Int) + d2692 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d108, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15042 p hg
    simpa only [d5537, d108, d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d108, d2692, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17320 p hg
    simpa only [d5537, d108, d2692, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17322 (p : Pattern) (guard : d0 p = 1) : d1881 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17323 (p : Pattern) (guard : d5502 p = 1) : d1882 p ≤ (0 : Int) + d2689 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1882, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2051 p hg
    simpa only [d5502, d1882, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1882, d2689, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17322 p hg
    simpa only [d5502, d1882, d2689, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17324 (p : Pattern) (guard : d1 p = 1) : d1881 p ≤ (0 : Int) + d1881 p := by
  omega
theorem compare17325 (p : Pattern) (guard : d5502 p = 1) : d1881 p ≤ (0 : Int) + d2693 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d2693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17324 p hg
    simpa only [d5502, d2693, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d2693, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17322 p hg
    simpa only [d5502, d2693, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17326 (p : Pattern) (guard : d5502 p = 1) : d1883 p ≤ (0 : Int) + d2694 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1883, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17323 p hg
    simpa only [d1883, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1883, d2694, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17325 p hg
    simpa only [d1883, d2694, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17327 (p : Pattern) (guard : d5537 p = 1) : d1884 p ≤ (0 : Int) + d2695 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1884, d2695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17326 p hg
    simpa only [d5537, d1884, d2695, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1884, d2695, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1884, d2695, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17328 (p : Pattern) (guard : d5537 p = 1) : d1885 p ≤ (0 : Int) + d2696 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1885, d2696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17321 p hg
    simpa only [d1885, d2696, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1885, d2696, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17327 p hg
    simpa only [d1885, d2696, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17329 (p : Pattern) (guard : d5537 p = 1) : d1886 p ≤ (0 : Int) + d2697 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1886, d2697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17318 p hg
    simpa only [d1886, d2697, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1886, d2697, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17328 p hg
    simpa only [d1886, d2697, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17330 (p : Pattern) (guard : d5537 p = 1) : d1887 p ≤ (0 : Int) + d2698 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1887, d2698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17319 p hg
    simpa only [d1887, d2698, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1887, d2698, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17329 p hg
    simpa only [d1887, d2698, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17331 (p : Pattern) (guard : d5537 p = 1) : d1888 p ≤ (0 : Int) + d2699 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1888, d2699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17180 p hg
    simpa only [d1888, d2699, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1888, d2699, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1888, d2699, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17332 (p : Pattern) (guard : d5537 p = 1) : d1889 p ≤ (0 : Int) + d2700 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1889, d2700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17329 p hg
    simpa only [d1889, d2700, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1889, d2700, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17331 p hg
    simpa only [d1889, d2700, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17333 (p : Pattern) (guard : d5537 p = 1) : d1890 p ≤ (0 : Int) + d2701 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1890, d2701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17330 p hg
    simpa only [d1890, d2701, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1890, d2701, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17332 p hg
    simpa only [d1890, d2701, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17334 (p : Pattern) (guard : d0 p = 1) : d1892 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17335 (p : Pattern) (guard : d5502 p = 1) : d1893 p ≤ (0 : Int) + d2702 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1893, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare2060 p hg
    simpa only [d5502, d1893, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1893, d2702, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17334 p hg
    simpa only [d5502, d1893, d2702, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17336 (p : Pattern) (guard : d1 p = 1) : d1895 p ≤ (0 : Int) + d1895 p := by
  omega
theorem compare17337 (p : Pattern) (guard : d0 p = 1) : d1896 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17338 (p : Pattern) (guard : d5502 p = 1) : d1897 p ≤ (0 : Int) + d2703 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1897, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17336 p hg
    simpa only [d5502, d1897, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1897, d2703, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17337 p hg
    simpa only [d5502, d1897, d2703, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17339 (p : Pattern) (guard : d5502 p = 1) : d1898 p ≤ (0 : Int) + d2704 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1898, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17335 p hg
    simpa only [d1898, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1898, d2704, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17338 p hg
    simpa only [d1898, d2704, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17340 (p : Pattern) (guard : d5537 p = 1) : d1899 p ≤ (0 : Int) + d2705 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1899, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17339 p hg
    simpa only [d5537, d1899, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1899, d2705, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1899, d2705, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17341 (p : Pattern) (guard : d5537 p = 1) : d1900 p ≤ (0 : Int) + d2706 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1900, d2706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17317 p hg
    simpa only [d1900, d2706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1900, d2706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17340 p hg
    simpa only [d1900, d2706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17342 (p : Pattern) (guard : d0 p = 1) : d317 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare17343 (p : Pattern) (guard : d5502 p = 1) : d1901 p ≤ (0 : Int) + d2707 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1901, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3159 p hg
    simpa only [d5502, d1901, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1901, d2707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17342 p hg
    simpa only [d5502, d1901, d2707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17344 (p : Pattern) (guard : d1 p = 1) : d1903 p ≤ (0 : Int) + d1903 p := by
  omega
theorem compare17345 (p : Pattern) (guard : d5502 p = 1) : d1904 p ≤ (0 : Int) + d2708 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5502, d1904, d2708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17344 p hg
    simpa only [d5502, d1904, d2708, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5502, d1904, d2708, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17342 p hg
    simpa only [d5502, d1904, d2708, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17346 (p : Pattern) (guard : d5502 p = 1) : d1905 p ≤ (0 : Int) + d2709 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d1905, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17343 p hg
    simpa only [d1905, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d1905, d2709, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17345 p hg
    simpa only [d1905, d2709, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17347 (p : Pattern) (guard : d5537 p = 1) : d1906 p ≤ (0 : Int) + d2710 p := by
  cases selected : p 204 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d5537, d1906, d2710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17346 p hg
    simpa only [d5537, d1906, d2710, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5537, d1906, d2710, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d5537, d1906, d2710, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17348 (p : Pattern) (guard : d5537 p = 1) : d1907 p ≤ (0 : Int) + d2711 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1907, d2711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17317 p hg
    simpa only [d1907, d2711, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1907, d2711, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17347 p hg
    simpa only [d1907, d2711, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17349 (p : Pattern) (guard : d5537 p = 1) : d1908 p ≤ (0 : Int) + d2712 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1908, d2712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17341 p hg
    simpa only [d1908, d2712, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1908, d2712, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17348 p hg
    simpa only [d1908, d2712, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17350 (p : Pattern) (guard : d5537 p = 1) : d1909 p ≤ (0 : Int) + d2713 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1909, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17317 p hg
    simpa only [d1909, d2713, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1909, d2713, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1909, d2713, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17351 (p : Pattern) (guard : d5537 p = 1) : d1910 p ≤ (0 : Int) + d2714 p := by
  cases selected : p 182 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1910, d2714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17321 p hg
    simpa only [d1910, d2714, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1910, d2714, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d1910, d2714, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17352 (p : Pattern) (guard : d5537 p = 1) : d1911 p ≤ (0 : Int) + d2715 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1911, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17350 p hg
    simpa only [d1911, d2715, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1911, d2715, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17351 p hg
    simpa only [d1911, d2715, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17353 (p : Pattern) (guard : d5537 p = 1) : d1912 p ≤ (0 : Int) + d2716 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1912, d2716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17349 p hg
    simpa only [d1912, d2716, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1912, d2716, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17352 p hg
    simpa only [d1912, d2716, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17354 (p : Pattern) (guard : d5537 p = 1) : d278 p ≤ (0 : Int) + d2717 p := by
  cases selected : p 163 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d278, d2717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17192 p hg
    simpa only [d278, d2717, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d278, d2717, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17119 p hg
    simpa only [d278, d2717, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17355 (p : Pattern) (guard : d5537 p = 1) : d1913 p ≤ (0 : Int) + d2718 p := by
  cases selected : p 162 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1913, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17352 p hg
    simpa only [d1913, d2718, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1913, d2718, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17354 p hg
    simpa only [d1913, d2718, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17356 (p : Pattern) (guard : d5537 p = 1) : d1914 p ≤ (0 : Int) + d2719 p := by
  cases selected : p 161 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1914, d2719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17353 p hg
    simpa only [d1914, d2719, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1914, d2719, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17355 p hg
    simpa only [d1914, d2719, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17357 (p : Pattern) (guard : d5537 p = 1) : d1915 p ≤ (0 : Int) + d2720 p := by
  cases selected : p 160 with
  | false =>
    have hg : d5537 p = 1 := by simpa only [d1915, d2720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17333 p hg
    simpa only [d1915, d2720, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5537 p = 1 := by simpa only [d1915, d2720, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17356 p hg
    simpa only [d1915, d2720, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17358 (p : Pattern) (guard : d5502 p = 1) : d103 p ≤ (0 : Int) + d2722 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5502 p = 1 := by simpa only [d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15077 p hg
    simpa only [d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5502 p = 1 := by simpa only [d2722, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15030 p hg
    simpa only [d2722, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare17359 (p : Pattern) (guard : d0 p = 1) : d333 p ≤ (0 : Int) + d2680 p := by
  change (0 : Int) = 1 at guard
  omega
end NetHack.Sokoban22Refined85
