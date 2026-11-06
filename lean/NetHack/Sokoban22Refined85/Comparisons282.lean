/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons281
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare39480 (p : Pattern) (guard : d8107 p = 1) : d1784 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1784, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39479 p hg
    simpa only [d8107, d1784, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1784, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39470 p hg
    simpa only [d8107, d1784, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39481 (p : Pattern) (guard : d8106 p = 1) : d1790 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1790, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35586 p hg
    simpa only [d8106, d1790, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1790, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38956 p hg
    simpa only [d8106, d1790, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39482 (p : Pattern) (guard : d8112 p = 1) : d1800 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1800, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39481 p hg
    simpa only [d8112, d1800, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1800, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38958 p hg
    simpa only [d8112, d1800, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39483 (p : Pattern) (guard : d8113 p = 1) : d1801 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1801, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39480 p hg
    simpa only [d8113, d1801, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1801, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39482 p hg
    simpa only [d8113, d1801, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39484 (p : Pattern) (guard : d8118 p = 1) : d1807 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1807, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39464 p hg
    simpa only [d8118, d1807, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1807, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38961 p hg
    simpa only [d8118, d1807, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39485 (p : Pattern) (guard : d8119 p = 1) : d1808 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1808, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39483 p hg
    simpa only [d8119, d1808, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1808, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39484 p hg
    simpa only [d8119, d1808, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39486 (p : Pattern) (guard : d8112 p = 1) : d1811 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1811, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38842 p hg
    simpa only [d8112, d1811, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1811, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38964 p hg
    simpa only [d8112, d1811, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39487 (p : Pattern) (guard : d8118 p = 1) : d1812 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1812, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39486 p hg
    simpa only [d8118, d1812, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1812, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38751 p hg
    simpa only [d8118, d1812, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39488 (p : Pattern) (guard : d8124 p = 1) : d1813 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1813, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39487 p hg
    simpa only [d8124, d1813, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1813, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1813, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39489 (p : Pattern) (guard : d8125 p = 1) : d1814 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1814, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39485 p hg
    simpa only [d8125, d1814, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1814, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39488 p hg
    simpa only [d8125, d1814, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39490 (p : Pattern) (guard : d8100 p = 1) : d15 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d15, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35482 p hg
    simpa only [d8100, d15, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d15, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d15, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39491 (p : Pattern) (guard : d8106 p = 1) : d1783 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1783, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39490 p hg
    simpa only [d8106, d1783, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1783, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38951 p hg
    simpa only [d8106, d1783, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39492 (p : Pattern) (guard : d8105 p = 1) : d32 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d32, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35627 p hg
    simpa only [d8105, d32, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d32, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d32, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39493 (p : Pattern) (guard : d8111 p = 1) : d1809 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1809, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39492 p hg
    simpa only [d8111, d1809, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1809, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15281 p hg
    simpa only [d8111, d1809, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39494 (p : Pattern) (guard : d8112 p = 1) : d1815 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1815, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39491 p hg
    simpa only [d8112, d1815, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1815, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39493 p hg
    simpa only [d8112, d1815, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39495 (p : Pattern) (guard : d8105 p = 1) : d19 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d19, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35489 p hg
    simpa only [d8105, d19, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d19, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d19, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39496 (p : Pattern) (guard : d8111 p = 1) : d1799 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1799, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39495 p hg
    simpa only [d8111, d1799, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1799, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15333 p hg
    simpa only [d8111, d1799, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39497 (p : Pattern) (guard : d8117 p = 1) : d1816 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1816, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39496 p hg
    simpa only [d8117, d1816, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1816, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38972 p hg
    simpa only [d8117, d1816, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39498 (p : Pattern) (guard : d8118 p = 1) : d1817 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1817, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39494 p hg
    simpa only [d8118, d1817, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1817, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39497 p hg
    simpa only [d8118, d1817, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39499 (p : Pattern) (guard : d8124 p = 1) : d1820 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1820, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39498 p hg
    simpa only [d8124, d1820, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1820, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38978 p hg
    simpa only [d8124, d1820, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39500 (p : Pattern) (guard : d8130 p = 1) : d1824 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1824, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39499 p hg
    simpa only [d8130, d1824, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1824, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38982 p hg
    simpa only [d8130, d1824, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39501 (p : Pattern) (guard : d8131 p = 1) : d1825 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1825, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39489 p hg
    simpa only [d8131, d1825, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1825, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39500 p hg
    simpa only [d8131, d1825, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39502 (p : Pattern) (guard : d8106 p = 1) : d1805 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1805, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38817 p hg
    simpa only [d8106, d1805, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1805, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38558 p hg
    simpa only [d8106, d1805, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39503 (p : Pattern) (guard : d8112 p = 1) : d1827 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1827, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39502 p hg
    simpa only [d8112, d1827, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1827, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38750 p hg
    simpa only [d8112, d1827, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39504 (p : Pattern) (guard : d8118 p = 1) : d1828 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1828, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39503 p hg
    simpa only [d8118, d1828, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1828, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38751 p hg
    simpa only [d8118, d1828, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39505 (p : Pattern) (guard : d8123 p = 1) : d1829 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38751 p hg
    simpa only [d8123, d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1829, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1829, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39506 (p : Pattern) (guard : d8124 p = 1) : d1830 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1830, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39504 p hg
    simpa only [d8124, d1830, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1830, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39505 p hg
    simpa only [d8124, d1830, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39507 (p : Pattern) (guard : d8129 p = 1) : d1831 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39505 p hg
    simpa only [d8129, d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1831, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1831, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39508 (p : Pattern) (guard : d8130 p = 1) : d1832 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1832, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39506 p hg
    simpa only [d8130, d1832, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1832, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39507 p hg
    simpa only [d8130, d1832, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39509 (p : Pattern) (guard : d8135 p = 1) : d1833 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39507 p hg
    simpa only [d8135, d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1833, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d1833, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39510 (p : Pattern) (guard : d8136 p = 1) : d1834 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1834, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39508 p hg
    simpa only [d8136, d1834, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1834, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39509 p hg
    simpa only [d8136, d1834, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39511 (p : Pattern) (guard : d8137 p = 1) : d1835 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1835, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39501 p hg
    simpa only [d8137, d1835, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1835, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39510 p hg
    simpa only [d8137, d1835, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39512 (p : Pattern) (guard : d8138 p = 1) : d1862 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1862, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39478 p hg
    simpa only [d8138, d1862, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1862, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39511 p hg
    simpa only [d8138, d1862, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39513 (p : Pattern) (guard : d8089 p = 1) : d1771 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1771, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34923 p hg
    simpa only [d8089, d1771, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1771, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38701 p hg
    simpa only [d8089, d1771, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39514 (p : Pattern) (guard : d8094 p = 1) : d1772 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1772, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39513 p hg
    simpa only [d8094, d1772, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1772, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38944 p hg
    simpa only [d8094, d1772, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39515 (p : Pattern) (guard : d8100 p = 1) : d1773 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1773, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39514 p hg
    simpa only [d8100, d1773, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1773, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1773, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39516 (p : Pattern) (guard : d8101 p = 1) : d1774 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1774, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39414 p hg
    simpa only [d8101, d1774, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1774, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39515 p hg
    simpa only [d8101, d1774, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39517 (p : Pattern) (guard : d5854 p = 1) : d1771 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34416 p hg
    simpa only [d5854, d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17200 p hg
    simpa only [d5854, d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39518 (p : Pattern) (guard : d8099 p = 1) : d1772 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39517 p hg
    simpa only [d8099, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17200 p hg
    simpa only [d8099, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39519 (p : Pattern) (guard : d8105 p = 1) : d1773 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39518 p hg
    simpa only [d8105, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39520 (p : Pattern) (guard : d8106 p = 1) : d1774 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1774, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39490 p hg
    simpa only [d8106, d1774, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1774, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39519 p hg
    simpa only [d8106, d1774, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39521 (p : Pattern) (guard : d8107 p = 1) : d1774 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39516 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39520 p hg
    simpa only [d8107, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39522 (p : Pattern) (guard : d8106 p = 1) : d1774 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1774, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39469 p hg
    simpa only [d8106, d1774, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1774, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39519 p hg
    simpa only [d8106, d1774, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39523 (p : Pattern) (guard : d8111 p = 1) : d2014 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2014, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39495 p hg
    simpa only [d8111, d2014, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2014, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15518 p hg
    simpa only [d8111, d2014, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39524 (p : Pattern) (guard : d8112 p = 1) : d2015 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2015, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39522 p hg
    simpa only [d8112, d2015, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2015, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39523 p hg
    simpa only [d8112, d2015, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39525 (p : Pattern) (guard : d8113 p = 1) : d2016 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d2016, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39521 p hg
    simpa only [d8113, d2016, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d2016, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39524 p hg
    simpa only [d8113, d2016, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39526 (p : Pattern) (guard : d8106 p = 1) : d1774 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1774, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35586 p hg
    simpa only [d8106, d1774, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1774, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39519 p hg
    simpa only [d8106, d1774, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39527 (p : Pattern) (guard : d8111 p = 1) : d2014 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34700 p hg
    simpa only [d8111, d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2014, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15518 p hg
    simpa only [d8111, d2014, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39528 (p : Pattern) (guard : d8112 p = 1) : d2015 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2015, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39526 p hg
    simpa only [d8112, d2015, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2015, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39527 p hg
    simpa only [d8112, d2015, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39529 (p : Pattern) (guard : d8118 p = 1) : d2017 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2017, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39528 p hg
    simpa only [d8118, d2017, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2017, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38961 p hg
    simpa only [d8118, d2017, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39530 (p : Pattern) (guard : d8119 p = 1) : d2018 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d2018, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39525 p hg
    simpa only [d8119, d2018, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d2018, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39529 p hg
    simpa only [d8119, d2018, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39531 (p : Pattern) (guard : d8111 p = 1) : d2019 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8111, d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2019, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15283 p hg
    simpa only [d8111, d2019, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39532 (p : Pattern) (guard : d8112 p = 1) : d2020 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2020, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38863 p hg
    simpa only [d8112, d2020, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2020, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39531 p hg
    simpa only [d8112, d2020, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39533 (p : Pattern) (guard : d8111 p = 1) : d2021 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8111, d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2021, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15286 p hg
    simpa only [d8111, d2021, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39534 (p : Pattern) (guard : d0 p = 1) : d2022 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39535 (p : Pattern) (guard : d8117 p = 1) : d2023 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39533 p hg
    simpa only [d8117, d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2023, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39534 p hg
    simpa only [d8117, d2023, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39536 (p : Pattern) (guard : d8118 p = 1) : d2024 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2024, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39532 p hg
    simpa only [d8118, d2024, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2024, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39535 p hg
    simpa only [d8118, d2024, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39537 (p : Pattern) (guard : d8117 p = 1) : d2025 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38931 p hg
    simpa only [d8117, d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2025, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39534 p hg
    simpa only [d8117, d2025, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39538 (p : Pattern) (guard : d8123 p = 1) : d2026 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39537 p hg
    simpa only [d8123, d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2026, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38938 p hg
    simpa only [d8123, d2026, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39539 (p : Pattern) (guard : d8124 p = 1) : d2027 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2027, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39536 p hg
    simpa only [d8124, d2027, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2027, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39538 p hg
    simpa only [d8124, d2027, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39540 (p : Pattern) (guard : d8125 p = 1) : d2028 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d2028, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39530 p hg
    simpa only [d8125, d2028, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d2028, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39539 p hg
    simpa only [d8125, d2028, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39541 (p : Pattern) (guard : d8100 p = 1) : d15 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d15, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35511 p hg
    simpa only [d8100, d15, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d15, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d15, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39542 (p : Pattern) (guard : d8106 p = 1) : d1774 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1774, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39541 p hg
    simpa only [d8106, d1774, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1774, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39519 p hg
    simpa only [d8106, d1774, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39543 (p : Pattern) (guard : d8105 p = 1) : d32 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d32, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35517 p hg
    simpa only [d8105, d32, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d32, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d32, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39544 (p : Pattern) (guard : d8111 p = 1) : d2032 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2032, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39543 p hg
    simpa only [d8111, d2032, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2032, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15534 p hg
    simpa only [d8111, d2032, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39545 (p : Pattern) (guard : d8112 p = 1) : d2033 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2033, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39542 p hg
    simpa only [d8112, d2033, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2033, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39544 p hg
    simpa only [d8112, d2033, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39546 (p : Pattern) (guard : d8105 p = 1) : d19 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d19, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35524 p hg
    simpa only [d8105, d19, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d19, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d19, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39547 (p : Pattern) (guard : d8111 p = 1) : d2014 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2014, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39546 p hg
    simpa only [d8111, d2014, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2014, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15518 p hg
    simpa only [d8111, d2014, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39548 (p : Pattern) (guard : d8117 p = 1) : d2034 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2034, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39547 p hg
    simpa only [d8117, d2034, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2034, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38972 p hg
    simpa only [d8117, d2034, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39549 (p : Pattern) (guard : d8118 p = 1) : d2035 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2035, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39545 p hg
    simpa only [d8118, d2035, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2035, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39548 p hg
    simpa only [d8118, d2035, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39550 (p : Pattern) (guard : d8117 p = 1) : d2036 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2036, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39523 p hg
    simpa only [d8117, d2036, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2036, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38975 p hg
    simpa only [d8117, d2036, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39551 (p : Pattern) (guard : d8123 p = 1) : d2037 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2037, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39550 p hg
    simpa only [d8123, d2037, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2037, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38977 p hg
    simpa only [d8123, d2037, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39552 (p : Pattern) (guard : d8124 p = 1) : d2038 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2038, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39549 p hg
    simpa only [d8124, d2038, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2038, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39551 p hg
    simpa only [d8124, d2038, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39553 (p : Pattern) (guard : d0 p = 1) : d1732 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39554 (p : Pattern) (guard : d8117 p = 1) : d2039 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39531 p hg
    simpa only [d8117, d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2039, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39553 p hg
    simpa only [d8117, d2039, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39555 (p : Pattern) (guard : d0 p = 1) : d2040 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39556 (p : Pattern) (guard : d8123 p = 1) : d2041 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39554 p hg
    simpa only [d8123, d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2041, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39555 p hg
    simpa only [d8123, d2041, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39557 (p : Pattern) (guard : d0 p = 1) : d2043 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39558 (p : Pattern) (guard : d8129 p = 1) : d2044 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39556 p hg
    simpa only [d8129, d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2044, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39557 p hg
    simpa only [d8129, d2044, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39559 (p : Pattern) (guard : d8130 p = 1) : d2045 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2045, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39552 p hg
    simpa only [d8130, d2045, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2045, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39558 p hg
    simpa only [d8130, d2045, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39560 (p : Pattern) (guard : d8131 p = 1) : d2046 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2046, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39540 p hg
    simpa only [d8131, d2046, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2046, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39559 p hg
    simpa only [d8131, d2046, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39561 (p : Pattern) (guard : d0 p = 1) : d2047 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39562 (p : Pattern) (guard : d8099 p = 1) : d2048 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38948 p hg
    simpa only [d8099, d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d2048, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39561 p hg
    simpa only [d8099, d2048, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39563 (p : Pattern) (guard : d8105 p = 1) : d2049 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39562 p hg
    simpa only [d8105, d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d2049, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d2049, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39564 (p : Pattern) (guard : d8106 p = 1) : d2050 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2050, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35586 p hg
    simpa only [d8106, d2050, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2050, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39563 p hg
    simpa only [d8106, d2050, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39565 (p : Pattern) (guard : d8111 p = 1) : d2056 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34908 p hg
    simpa only [d8111, d2056, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2056, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15552 p hg
    simpa only [d8111, d2056, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39566 (p : Pattern) (guard : d8112 p = 1) : d2057 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2057, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39564 p hg
    simpa only [d8112, d2057, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2057, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39565 p hg
    simpa only [d8112, d2057, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39567 (p : Pattern) (guard : d0 p = 1) : d1810 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39568 (p : Pattern) (guard : d8117 p = 1) : d1811 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38970 p hg
    simpa only [d8117, d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39567 p hg
    simpa only [d8117, d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39569 (p : Pattern) (guard : d8118 p = 1) : d2058 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2058, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39566 p hg
    simpa only [d8118, d2058, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2058, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39568 p hg
    simpa only [d8118, d2058, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39570 (p : Pattern) (guard : d8123 p = 1) : d1812 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39568 p hg
    simpa only [d8123, d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38977 p hg
    simpa only [d8123, d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39571 (p : Pattern) (guard : d8124 p = 1) : d2059 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2059, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39569 p hg
    simpa only [d8124, d2059, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2059, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39570 p hg
    simpa only [d8124, d2059, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39572 (p : Pattern) (guard : d0 p = 1) : d2063 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39573 (p : Pattern) (guard : d8117 p = 1) : d2064 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38958 p hg
    simpa only [d8117, d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39572 p hg
    simpa only [d8117, d2064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39574 (p : Pattern) (guard : d8123 p = 1) : d2065 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39573 p hg
    simpa only [d8123, d2065, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2065, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2065, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39575 (p : Pattern) (guard : d8129 p = 1) : d2066 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39574 p hg
    simpa only [d8129, d2066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d2066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39576 (p : Pattern) (guard : d8130 p = 1) : d2067 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2067, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39571 p hg
    simpa only [d8130, d2067, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2067, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39575 p hg
    simpa only [d8130, d2067, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39577 (p : Pattern) (guard : d8111 p = 1) : d2073 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2073, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39471 p hg
    simpa only [d8111, d2073, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2073, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15565 p hg
    simpa only [d8111, d2073, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39578 (p : Pattern) (guard : d0 p = 1) : d1809 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39579 (p : Pattern) (guard : d8117 p = 1) : d2074 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2074, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39577 p hg
    simpa only [d8117, d2074, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2074, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39578 p hg
    simpa only [d8117, d2074, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39580 (p : Pattern) (guard : d0 p = 1) : d2075 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39581 (p : Pattern) (guard : d8123 p = 1) : d2076 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2076, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39579 p hg
    simpa only [d8123, d2076, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2076, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39580 p hg
    simpa only [d8123, d2076, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39582 (p : Pattern) (guard : d0 p = 1) : d1822 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39583 (p : Pattern) (guard : d8129 p = 1) : d2077 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2077, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39581 p hg
    simpa only [d8129, d2077, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2077, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39582 p hg
    simpa only [d8129, d2077, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39584 (p : Pattern) (guard : d0 p = 1) : d2080 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39585 (p : Pattern) (guard : d8135 p = 1) : d2081 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2081, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39583 p hg
    simpa only [d8135, d2081, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2081, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39584 p hg
    simpa only [d8135, d2081, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39586 (p : Pattern) (guard : d8136 p = 1) : d2082 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2082, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39576 p hg
    simpa only [d8136, d2082, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2082, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39585 p hg
    simpa only [d8136, d2082, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39587 (p : Pattern) (guard : d8137 p = 1) : d2083 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2083, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39560 p hg
    simpa only [d8137, d2083, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2083, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39586 p hg
    simpa only [d8137, d2083, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39588 (p : Pattern) (guard : d8106 p = 1) : d2050 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d2050, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39469 p hg
    simpa only [d8106, d2050, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d2050, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39563 p hg
    simpa only [d8106, d2050, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39589 (p : Pattern) (guard : d8105 p = 1) : d15 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d15, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35551 p hg
    simpa only [d8105, d15, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d15, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d15, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39590 (p : Pattern) (guard : d8111 p = 1) : d2056 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2056, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39589 p hg
    simpa only [d8111, d2056, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2056, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15552 p hg
    simpa only [d8111, d2056, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39591 (p : Pattern) (guard : d8112 p = 1) : d2057 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d2057, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39588 p hg
    simpa only [d8112, d2057, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d2057, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39590 p hg
    simpa only [d8112, d2057, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39592 (p : Pattern) (guard : d8118 p = 1) : d2058 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2058, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39591 p hg
    simpa only [d8118, d2058, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2058, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39568 p hg
    simpa only [d8118, d2058, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39593 (p : Pattern) (guard : d8124 p = 1) : d2059 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2059, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39592 p hg
    simpa only [d8124, d2059, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2059, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39570 p hg
    simpa only [d8124, d2059, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39594 (p : Pattern) (guard : d8130 p = 1) : d2067 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2067, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39593 p hg
    simpa only [d8130, d2067, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2067, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39575 p hg
    simpa only [d8130, d2067, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39595 (p : Pattern) (guard : d8111 p = 1) : d2073 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2073, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39492 p hg
    simpa only [d8111, d2073, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2073, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15565 p hg
    simpa only [d8111, d2073, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39596 (p : Pattern) (guard : d8117 p = 1) : d2074 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2074, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39595 p hg
    simpa only [d8117, d2074, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2074, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39578 p hg
    simpa only [d8117, d2074, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39597 (p : Pattern) (guard : d8123 p = 1) : d2076 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2076, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39596 p hg
    simpa only [d8123, d2076, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2076, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39580 p hg
    simpa only [d8123, d2076, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39598 (p : Pattern) (guard : d8129 p = 1) : d2077 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2077, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39597 p hg
    simpa only [d8129, d2077, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2077, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39582 p hg
    simpa only [d8129, d2077, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39599 (p : Pattern) (guard : d8135 p = 1) : d2081 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2081, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39598 p hg
    simpa only [d8135, d2081, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2081, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39584 p hg
    simpa only [d8135, d2081, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39600 (p : Pattern) (guard : d8136 p = 1) : d2082 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2082, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39594 p hg
    simpa only [d8136, d2082, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2082, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39599 p hg
    simpa only [d8136, d2082, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39601 (p : Pattern) (guard : d8142 p = 1) : d2084 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d2084, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39600 p hg
    simpa only [d8142, d2084, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d2084, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d2084, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39602 (p : Pattern) (guard : d8143 p = 1) : d2085 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d2085, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39587 p hg
    simpa only [d8143, d2085, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d2085, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39601 p hg
    simpa only [d8143, d2085, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39603 (p : Pattern) (guard : d8144 p = 1) : d2086 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d2086, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39512 p hg
    simpa only [d8144, d2086, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d2086, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39602 p hg
    simpa only [d8144, d2086, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39604 (p : Pattern) (guard : d8145 p = 1) : d2087 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8139 p = 1 := by simpa only [d8145, d2087, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39133 p hg
    simpa only [d8145, d2087, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8144 p = 1 := by simpa only [d8145, d2087, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39603 p hg
    simpa only [d8145, d2087, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39605 (p : Pattern) (guard : d8090 p = 1) : d321 p ≤ (0 : Int) + d321 p := by
  omega
theorem compare39606 (p : Pattern) (guard : d8091 p = 1) : d1682 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d1682, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35563 p hg
    simpa only [d8091, d1682, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d1682, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39605 p hg
    simpa only [d8091, d1682, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39607 (p : Pattern) (guard : d8085 p = 1) : d1685 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1685, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34321 p hg
    simpa only [d8085, d1685, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1685, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38345 p hg
    simpa only [d8085, d1685, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39608 (p : Pattern) (guard : d8090 p = 1) : d1686 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1686, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39607 p hg
    simpa only [d8090, d1686, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1686, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38632 p hg
    simpa only [d8090, d1686, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39609 (p : Pattern) (guard : d8095 p = 1) : d1687 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1687, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39608 p hg
    simpa only [d8095, d1687, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1687, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1687, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39610 (p : Pattern) (guard : d8096 p = 1) : d1688 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1688, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39606 p hg
    simpa only [d8096, d1688, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1688, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39609 p hg
    simpa only [d8096, d1688, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39611 (p : Pattern) (guard : d8102 p = 1) : d1691 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1691, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39610 p hg
    simpa only [d8102, d1691, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1691, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39440 p hg
    simpa only [d8102, d1691, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39612 (p : Pattern) (guard : d8107 p = 1) : d1699 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1699, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39418 p hg
    simpa only [d8107, d1699, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1699, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39445 p hg
    simpa only [d8107, d1699, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39613 (p : Pattern) (guard : d8108 p = 1) : d1700 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1700, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39611 p hg
    simpa only [d8108, d1700, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1700, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39612 p hg
    simpa only [d8108, d1700, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39614 (p : Pattern) (guard : d8112 p = 1) : d1707 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1707, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39034 p hg
    simpa only [d8112, d1707, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1707, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1707, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39615 (p : Pattern) (guard : d8113 p = 1) : d1708 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1708, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39422 p hg
    simpa only [d8113, d1708, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1708, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39614 p hg
    simpa only [d8113, d1708, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39616 (p : Pattern) (guard : d8114 p = 1) : d1709 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1709, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39613 p hg
    simpa only [d8114, d1709, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1709, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39615 p hg
    simpa only [d8114, d1709, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39617 (p : Pattern) (guard : d8101 p = 1) : d1719 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1719, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38915 p hg
    simpa only [d8101, d1719, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1719, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d8101, d1719, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39618 (p : Pattern) (guard : d8107 p = 1) : d1727 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1727, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39617 p hg
    simpa only [d8107, d1727, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1727, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39455 p hg
    simpa only [d8107, d1727, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39619 (p : Pattern) (guard : d8106 p = 1) : d1731 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1731, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35414 p hg
    simpa only [d8106, d1731, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1731, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38569 p hg
    simpa only [d8106, d1731, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
