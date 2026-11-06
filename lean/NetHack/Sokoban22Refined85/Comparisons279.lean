/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons278
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare39060 (p : Pattern) (guard : d8108 p = 1) : d1801 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1801, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39057 p hg
    simpa only [d8108, d1801, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1801, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39059 p hg
    simpa only [d8108, d1801, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39061 (p : Pattern) (guard : d8113 p = 1) : d1807 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1807, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38852 p hg
    simpa only [d8113, d1807, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1807, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38725 p hg
    simpa only [d8113, d1807, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39062 (p : Pattern) (guard : d8114 p = 1) : d1808 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1808, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39060 p hg
    simpa only [d8114, d1808, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1808, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39061 p hg
    simpa only [d8114, d1808, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39063 (p : Pattern) (guard : d8107 p = 1) : d1811 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1811, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38552 p hg
    simpa only [d8107, d1811, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1811, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38733 p hg
    simpa only [d8107, d1811, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39064 (p : Pattern) (guard : d8113 p = 1) : d1812 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1812, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39063 p hg
    simpa only [d8113, d1812, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1812, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38571 p hg
    simpa only [d8113, d1812, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39065 (p : Pattern) (guard : d8119 p = 1) : d1813 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1813, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39064 p hg
    simpa only [d8119, d1813, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1813, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1813, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39066 (p : Pattern) (guard : d8120 p = 1) : d1814 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1814, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39062 p hg
    simpa only [d8120, d1814, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1814, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39065 p hg
    simpa only [d8120, d1814, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39067 (p : Pattern) (guard : d8101 p = 1) : d1783 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1783, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38915 p hg
    simpa only [d8101, d1783, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1783, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38711 p hg
    simpa only [d8101, d1783, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39068 (p : Pattern) (guard : d8106 p = 1) : d1809 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1809, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38917 p hg
    simpa only [d8106, d1809, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1809, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38742 p hg
    simpa only [d8106, d1809, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39069 (p : Pattern) (guard : d8107 p = 1) : d1815 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1815, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39067 p hg
    simpa only [d8107, d1815, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1815, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39068 p hg
    simpa only [d8107, d1815, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39070 (p : Pattern) (guard : d8106 p = 1) : d1799 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1799, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38923 p hg
    simpa only [d8106, d1799, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1799, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38721 p hg
    simpa only [d8106, d1799, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39071 (p : Pattern) (guard : d8112 p = 1) : d1816 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1816, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39070 p hg
    simpa only [d8112, d1816, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1816, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38745 p hg
    simpa only [d8112, d1816, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39072 (p : Pattern) (guard : d8113 p = 1) : d1817 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1817, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39069 p hg
    simpa only [d8113, d1817, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1817, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39071 p hg
    simpa only [d8113, d1817, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39073 (p : Pattern) (guard : d8112 p = 1) : d1818 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1818, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38866 p hg
    simpa only [d8112, d1818, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1818, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38748 p hg
    simpa only [d8112, d1818, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39074 (p : Pattern) (guard : d8118 p = 1) : d1819 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1819, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39073 p hg
    simpa only [d8118, d1819, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1819, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38751 p hg
    simpa only [d8118, d1819, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39075 (p : Pattern) (guard : d8119 p = 1) : d1820 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1820, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39072 p hg
    simpa only [d8119, d1820, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1820, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39074 p hg
    simpa only [d8119, d1820, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39076 (p : Pattern) (guard : d8125 p = 1) : d1824 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1824, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39075 p hg
    simpa only [d8125, d1824, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1824, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38756 p hg
    simpa only [d8125, d1824, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39077 (p : Pattern) (guard : d8126 p = 1) : d1825 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1825, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39066 p hg
    simpa only [d8126, d1825, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1825, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39076 p hg
    simpa only [d8126, d1825, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39078 (p : Pattern) (guard : d8101 p = 1) : d1805 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1805, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38440 p hg
    simpa only [d8101, d1805, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1805, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38516 p hg
    simpa only [d8101, d1805, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39079 (p : Pattern) (guard : d8107 p = 1) : d1827 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1827, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39078 p hg
    simpa only [d8107, d1827, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1827, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38570 p hg
    simpa only [d8107, d1827, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39080 (p : Pattern) (guard : d8113 p = 1) : d1828 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1828, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39079 p hg
    simpa only [d8113, d1828, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1828, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38571 p hg
    simpa only [d8113, d1828, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39081 (p : Pattern) (guard : d8119 p = 1) : d1830 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1830, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39080 p hg
    simpa only [d8119, d1830, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1830, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38875 p hg
    simpa only [d8119, d1830, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39082 (p : Pattern) (guard : d8125 p = 1) : d1832 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1832, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39081 p hg
    simpa only [d8125, d1832, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1832, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38877 p hg
    simpa only [d8125, d1832, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39083 (p : Pattern) (guard : d8118 p = 1) : d1829 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1829, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39042 p hg
    simpa only [d8118, d1829, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1829, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1829, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39084 (p : Pattern) (guard : d8124 p = 1) : d1831 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1831, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39083 p hg
    simpa only [d8124, d1831, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1831, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1831, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39085 (p : Pattern) (guard : d8130 p = 1) : d1833 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1833, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39084 p hg
    simpa only [d8130, d1833, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1833, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d1833, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39086 (p : Pattern) (guard : d8131 p = 1) : d1834 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1834, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39082 p hg
    simpa only [d8131, d1834, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1834, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39085 p hg
    simpa only [d8131, d1834, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39087 (p : Pattern) (guard : d8132 p = 1) : d1835 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1835, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39077 p hg
    simpa only [d8132, d1835, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1835, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39086 p hg
    simpa only [d8132, d1835, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39088 (p : Pattern) (guard : d8133 p = 1) : d1836 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d1836, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39052 p hg
    simpa only [d8133, d1836, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d1836, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39087 p hg
    simpa only [d8133, d1836, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39089 (p : Pattern) (guard : d8102 p = 1) : d1837 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1837, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38811 p hg
    simpa only [d8102, d1837, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1837, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38916 p hg
    simpa only [d8102, d1837, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39090 (p : Pattern) (guard : d8107 p = 1) : d1699 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1699, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38887 p hg
    simpa only [d8107, d1699, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1699, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38924 p hg
    simpa only [d8107, d1699, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39091 (p : Pattern) (guard : d8108 p = 1) : d1838 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1838, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39089 p hg
    simpa only [d8108, d1838, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1838, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39090 p hg
    simpa only [d8108, d1838, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39092 (p : Pattern) (guard : d8113 p = 1) : d1708 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1708, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38894 p hg
    simpa only [d8113, d1708, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1708, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38899 p hg
    simpa only [d8113, d1708, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39093 (p : Pattern) (guard : d8114 p = 1) : d1839 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1839, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39091 p hg
    simpa only [d8114, d1839, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1839, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39092 p hg
    simpa only [d8114, d1839, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39094 (p : Pattern) (guard : d8101 p = 1) : d1719 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1719, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34967 p hg
    simpa only [d8101, d1719, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1719, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38551 p hg
    simpa only [d8101, d1719, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39095 (p : Pattern) (guard : d8107 p = 1) : d1727 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1727, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39094 p hg
    simpa only [d8107, d1727, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1727, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38903 p hg
    simpa only [d8107, d1727, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39096 (p : Pattern) (guard : d8113 p = 1) : d1734 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1734, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39095 p hg
    simpa only [d8113, d1734, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1734, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38907 p hg
    simpa only [d8113, d1734, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39097 (p : Pattern) (guard : d8119 p = 1) : d1738 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1738, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39096 p hg
    simpa only [d8119, d1738, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1738, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38912 p hg
    simpa only [d8119, d1738, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39098 (p : Pattern) (guard : d8120 p = 1) : d1840 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1840, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39093 p hg
    simpa only [d8120, d1840, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1840, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39097 p hg
    simpa only [d8120, d1840, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39099 (p : Pattern) (guard : d8095 p = 1) : d15 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d15, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35040 p hg
    simpa only [d8095, d15, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d15, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d15, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39100 (p : Pattern) (guard : d8101 p = 1) : d1692 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1692, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39099 p hg
    simpa only [d8101, d1692, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1692, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38886 p hg
    simpa only [d8101, d1692, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39101 (p : Pattern) (guard : d8100 p = 1) : d32 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d32, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35045 p hg
    simpa only [d8100, d32, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d32, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d32, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39102 (p : Pattern) (guard : d8106 p = 1) : d1747 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1747, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39101 p hg
    simpa only [d8106, d1747, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1747, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38920 p hg
    simpa only [d8106, d1747, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39103 (p : Pattern) (guard : d8107 p = 1) : d1841 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1841, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39100 p hg
    simpa only [d8107, d1841, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1841, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39102 p hg
    simpa only [d8107, d1841, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39104 (p : Pattern) (guard : d8100 p = 1) : d19 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d19, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35051 p hg
    simpa only [d8100, d19, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d19, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d19, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39105 (p : Pattern) (guard : d8106 p = 1) : d1698 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1698, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39104 p hg
    simpa only [d8106, d1698, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1698, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38892 p hg
    simpa only [d8106, d1698, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39106 (p : Pattern) (guard : d8112 p = 1) : d1749 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1749, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39105 p hg
    simpa only [d8112, d1749, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1749, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38925 p hg
    simpa only [d8112, d1749, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39107 (p : Pattern) (guard : d8113 p = 1) : d1842 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1842, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39103 p hg
    simpa only [d8113, d1842, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1842, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39106 p hg
    simpa only [d8113, d1842, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39108 (p : Pattern) (guard : d8112 p = 1) : d1755 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1755, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38924 p hg
    simpa only [d8112, d1755, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1755, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38748 p hg
    simpa only [d8112, d1755, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39109 (p : Pattern) (guard : d8118 p = 1) : d1758 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1758, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39108 p hg
    simpa only [d8118, d1758, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1758, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38751 p hg
    simpa only [d8118, d1758, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39110 (p : Pattern) (guard : d8119 p = 1) : d1843 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1843, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39107 p hg
    simpa only [d8119, d1843, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1843, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39109 p hg
    simpa only [d8119, d1843, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39111 (p : Pattern) (guard : d8106 p = 1) : d1726 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1726, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35389 p hg
    simpa only [d8106, d1726, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1726, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38732 p hg
    simpa only [d8106, d1726, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39112 (p : Pattern) (guard : d8112 p = 1) : d1761 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1761, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39111 p hg
    simpa only [d8112, d1761, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1761, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38931 p hg
    simpa only [d8112, d1761, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39113 (p : Pattern) (guard : d8118 p = 1) : d1763 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1763, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39112 p hg
    simpa only [d8118, d1763, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1763, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38934 p hg
    simpa only [d8118, d1763, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39114 (p : Pattern) (guard : d8124 p = 1) : d1766 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1766, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39113 p hg
    simpa only [d8124, d1766, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1766, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38939 p hg
    simpa only [d8124, d1766, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39115 (p : Pattern) (guard : d8125 p = 1) : d1844 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1844, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39110 p hg
    simpa only [d8125, d1844, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1844, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39114 p hg
    simpa only [d8125, d1844, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39116 (p : Pattern) (guard : d8126 p = 1) : d1845 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1845, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39098 p hg
    simpa only [d8126, d1845, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1845, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39115 p hg
    simpa only [d8126, d1845, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39117 (p : Pattern) (guard : d8132 p = 1) : d1846 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1846, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39116 p hg
    simpa only [d8132, d1846, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1846, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38996 p hg
    simpa only [d8132, d1846, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39118 (p : Pattern) (guard : d8101 p = 1) : d1774 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1774, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35565 p hg
    simpa only [d8101, d1774, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1774, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38946 p hg
    simpa only [d8101, d1774, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39119 (p : Pattern) (guard : d8107 p = 1) : d1784 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1784, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39118 p hg
    simpa only [d8107, d1784, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1784, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38991 p hg
    simpa only [d8107, d1784, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39120 (p : Pattern) (guard : d8106 p = 1) : d1790 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1790, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35389 p hg
    simpa only [d8106, d1790, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1790, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38956 p hg
    simpa only [d8106, d1790, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39121 (p : Pattern) (guard : d8112 p = 1) : d1800 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1800, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39120 p hg
    simpa only [d8112, d1800, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1800, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38958 p hg
    simpa only [d8112, d1800, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39122 (p : Pattern) (guard : d8113 p = 1) : d1801 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1801, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39119 p hg
    simpa only [d8113, d1801, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1801, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39121 p hg
    simpa only [d8113, d1801, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39123 (p : Pattern) (guard : d8119 p = 1) : d1808 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1808, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39122 p hg
    simpa only [d8119, d1808, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1808, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38962 p hg
    simpa only [d8119, d1808, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39124 (p : Pattern) (guard : d8125 p = 1) : d1814 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1814, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39123 p hg
    simpa only [d8125, d1814, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1814, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38967 p hg
    simpa only [d8125, d1814, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39125 (p : Pattern) (guard : d8106 p = 1) : d1783 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1783, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35586 p hg
    simpa only [d8106, d1783, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1783, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38951 p hg
    simpa only [d8106, d1783, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39126 (p : Pattern) (guard : d8112 p = 1) : d1815 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1815, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39125 p hg
    simpa only [d8112, d1815, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1815, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38970 p hg
    simpa only [d8112, d1815, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39127 (p : Pattern) (guard : d8118 p = 1) : d1817 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1817, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39126 p hg
    simpa only [d8118, d1817, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1817, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38973 p hg
    simpa only [d8118, d1817, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39128 (p : Pattern) (guard : d8124 p = 1) : d1820 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1820, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39127 p hg
    simpa only [d8124, d1820, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1820, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38978 p hg
    simpa only [d8124, d1820, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39129 (p : Pattern) (guard : d8130 p = 1) : d1824 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1824, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39128 p hg
    simpa only [d8130, d1824, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1824, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38982 p hg
    simpa only [d8130, d1824, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39130 (p : Pattern) (guard : d8131 p = 1) : d1825 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1825, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39124 p hg
    simpa only [d8131, d1825, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1825, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39129 p hg
    simpa only [d8131, d1825, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39131 (p : Pattern) (guard : d8137 p = 1) : d1847 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1847, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39130 p hg
    simpa only [d8137, d1847, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1847, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d1847, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39132 (p : Pattern) (guard : d8138 p = 1) : d1848 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1848, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39117 p hg
    simpa only [d8138, d1848, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1848, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39131 p hg
    simpa only [d8138, d1848, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39133 (p : Pattern) (guard : d8139 p = 1) : d1849 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d1849, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39088 p hg
    simpa only [d8139, d1849, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d1849, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39132 p hg
    simpa only [d8139, d1849, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39134 (p : Pattern) (guard : d8090 p = 1) : d358 p ≤ (0 : Int) + d358 p := by
  omega
theorem compare39135 (p : Pattern) (guard : d8091 p = 1) : d1871 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d1871, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35096 p hg
    simpa only [d8091, d1871, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d1871, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39134 p hg
    simpa only [d8091, d1871, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39136 (p : Pattern) (guard : d1 p = 1) : d1872 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1571 p hg
    simpa only [d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39137 (p : Pattern) (guard : d8084 p = 1) : d1873 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39136 p hg
    simpa only [d8084, d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35165 p hg
    simpa only [d8084, d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39138 (p : Pattern) (guard : d8085 p = 1) : d1874 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1874, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35092 p hg
    simpa only [d8085, d1874, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1874, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39137 p hg
    simpa only [d8085, d1874, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39139 (p : Pattern) (guard : d5843 p = 1) : d1872 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1561 p hg
    simpa only [d5843, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1872, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20196 p hg
    simpa only [d5843, d1872, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39140 (p : Pattern) (guard : d5847 p = 1) : d1873 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39139 p hg
    simpa only [d5847, d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17806 p hg
    simpa only [d5847, d1873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39141 (p : Pattern) (guard : d8089 p = 1) : d1873 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39137 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39140 p hg
    simpa only [d8089, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39142 (p : Pattern) (guard : d8090 p = 1) : d1875 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1875, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39138 p hg
    simpa only [d8090, d1875, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1875, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39141 p hg
    simpa only [d8090, d1875, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39143 (p : Pattern) (guard : d8095 p = 1) : d1876 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1876, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39142 p hg
    simpa only [d8095, d1876, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1876, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1876, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39144 (p : Pattern) (guard : d8096 p = 1) : d1877 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1877, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39135 p hg
    simpa only [d8096, d1877, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1877, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39143 p hg
    simpa only [d8096, d1877, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39145 (p : Pattern) (guard : d8095 p = 1) : d104 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d104, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35113 p hg
    simpa only [d8095, d104, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d104, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d104, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39146 (p : Pattern) (guard : d8089 p = 1) : d1874 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1874, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35111 p hg
    simpa only [d8089, d1874, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1874, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39140 p hg
    simpa only [d8089, d1874, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39147 (p : Pattern) (guard : d5854 p = 1) : d1873 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39140 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17309 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39148 (p : Pattern) (guard : d8094 p = 1) : d1875 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1875, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39146 p hg
    simpa only [d8094, d1875, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1875, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39147 p hg
    simpa only [d8094, d1875, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39149 (p : Pattern) (guard : d8100 p = 1) : d1876 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1876, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39148 p hg
    simpa only [d8100, d1876, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1876, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1876, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39150 (p : Pattern) (guard : d8101 p = 1) : d1878 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1878, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39145 p hg
    simpa only [d8101, d1878, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1878, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39149 p hg
    simpa only [d8101, d1878, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39151 (p : Pattern) (guard : d8102 p = 1) : d1879 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1879, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39144 p hg
    simpa only [d8102, d1879, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1879, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39150 p hg
    simpa only [d8102, d1879, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39152 (p : Pattern) (guard : d8095 p = 1) : d104 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d104, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35124 p hg
    simpa only [d8095, d104, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d104, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d104, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39153 (p : Pattern) (guard : d8089 p = 1) : d1874 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35094 p hg
    simpa only [d8089, d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1874, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39140 p hg
    simpa only [d8089, d1874, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39154 (p : Pattern) (guard : d8094 p = 1) : d1875 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39153 p hg
    simpa only [d8094, d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1875, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39147 p hg
    simpa only [d8094, d1875, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39155 (p : Pattern) (guard : d8100 p = 1) : d1876 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39154 p hg
    simpa only [d8100, d1876, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1876, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1876, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39156 (p : Pattern) (guard : d8101 p = 1) : d1878 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1878, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39152 p hg
    simpa only [d8101, d1878, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1878, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39155 p hg
    simpa only [d8101, d1878, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39157 (p : Pattern) (guard : d8100 p = 1) : d108 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d108, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35136 p hg
    simpa only [d8100, d108, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d108, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d108, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39158 (p : Pattern) (guard : d5854 p = 1) : d1882 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35133 p hg
    simpa only [d5854, d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1882, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17322 p hg
    simpa only [d5854, d1882, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39159 (p : Pattern) (guard : d8099 p = 1) : d1883 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39158 p hg
    simpa only [d8099, d1883, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1883, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17322 p hg
    simpa only [d8099, d1883, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39160 (p : Pattern) (guard : d8105 p = 1) : d1884 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39159 p hg
    simpa only [d8105, d1884, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1884, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1884, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39161 (p : Pattern) (guard : d8106 p = 1) : d1885 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1885, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39157 p hg
    simpa only [d8106, d1885, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1885, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39160 p hg
    simpa only [d8106, d1885, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39162 (p : Pattern) (guard : d8107 p = 1) : d1886 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1886, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39156 p hg
    simpa only [d8107, d1886, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1886, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39161 p hg
    simpa only [d8107, d1886, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39163 (p : Pattern) (guard : d8108 p = 1) : d1887 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1887, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39151 p hg
    simpa only [d8108, d1887, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1887, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39162 p hg
    simpa only [d8108, d1887, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39164 (p : Pattern) (guard : d8095 p = 1) : d104 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d104, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35147 p hg
    simpa only [d8095, d104, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d104, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d104, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39165 (p : Pattern) (guard : d8101 p = 1) : d1878 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1878, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39164 p hg
    simpa only [d8101, d1878, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1878, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39155 p hg
    simpa only [d8101, d1878, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39166 (p : Pattern) (guard : d8100 p = 1) : d108 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d108, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35153 p hg
    simpa only [d8100, d108, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d108, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d108, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39167 (p : Pattern) (guard : d8106 p = 1) : d1885 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1885, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39166 p hg
    simpa only [d8106, d1885, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1885, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39160 p hg
    simpa only [d8106, d1885, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39168 (p : Pattern) (guard : d8107 p = 1) : d1886 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1886, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39165 p hg
    simpa only [d8107, d1886, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1886, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39167 p hg
    simpa only [d8107, d1886, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39169 (p : Pattern) (guard : d8112 p = 1) : d1888 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1888, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39038 p hg
    simpa only [d8112, d1888, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1888, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1888, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39170 (p : Pattern) (guard : d8113 p = 1) : d1889 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1889, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39168 p hg
    simpa only [d8113, d1889, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1889, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39169 p hg
    simpa only [d8113, d1889, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39171 (p : Pattern) (guard : d8114 p = 1) : d1890 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1890, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39163 p hg
    simpa only [d8114, d1890, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1890, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39170 p hg
    simpa only [d8114, d1890, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39172 (p : Pattern) (guard : d8095 p = 1) : d104 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d104, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35163 p hg
    simpa only [d8095, d104, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d104, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d104, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39173 (p : Pattern) (guard : d5843 p = 1) : d1891 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1571 p hg
    simpa only [d5843, d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1891, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare19887 p hg
    simpa only [d5843, d1891, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39174 (p : Pattern) (guard : d5847 p = 1) : d1892 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39173 p hg
    simpa only [d5847, d1892, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1892, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17666 p hg
    simpa only [d5847, d1892, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39175 (p : Pattern) (guard : d8089 p = 1) : d1893 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35166 p hg
    simpa only [d8089, d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1893, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39174 p hg
    simpa only [d8089, d1893, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39176 (p : Pattern) (guard : d5843 p = 1) : d1894 p ≤ (0 : Int) + d12 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d5843, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1571 p hg
    simpa only [d5843, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5843, d1894, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare20207 p hg
    simpa only [d5843, d1894, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39177 (p : Pattern) (guard : d5847 p = 1) : d1895 p ≤ (0 : Int) + d12 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39176 p hg
    simpa only [d5847, d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d1895, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17810 p hg
    simpa only [d5847, d1895, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39178 (p : Pattern) (guard : d5854 p = 1) : d1897 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39177 p hg
    simpa only [d5854, d1897, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1897, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17337 p hg
    simpa only [d5854, d1897, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39179 (p : Pattern) (guard : d8094 p = 1) : d1898 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39175 p hg
    simpa only [d8094, d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1898, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39178 p hg
    simpa only [d8094, d1898, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39180 (p : Pattern) (guard : d8100 p = 1) : d1899 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39179 p hg
    simpa only [d8100, d1899, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1899, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1899, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39181 (p : Pattern) (guard : d8101 p = 1) : d1900 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1900, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39172 p hg
    simpa only [d8101, d1900, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1900, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39180 p hg
    simpa only [d8101, d1900, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39182 (p : Pattern) (guard : d5854 p = 1) : d1901 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35181 p hg
    simpa only [d5854, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1901, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17342 p hg
    simpa only [d5854, d1901, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39183 (p : Pattern) (guard : d0 p = 1) : d1904 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39184 (p : Pattern) (guard : d8099 p = 1) : d1905 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39182 p hg
    simpa only [d8099, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1905, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39183 p hg
    simpa only [d8099, d1905, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39185 (p : Pattern) (guard : d8105 p = 1) : d1906 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39184 p hg
    simpa only [d8105, d1906, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1906, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1906, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39186 (p : Pattern) (guard : d8106 p = 1) : d1907 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1907, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35205 p hg
    simpa only [d8106, d1907, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1907, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39185 p hg
    simpa only [d8106, d1907, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39187 (p : Pattern) (guard : d8107 p = 1) : d1908 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1908, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39181 p hg
    simpa only [d8107, d1908, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1908, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39186 p hg
    simpa only [d8107, d1908, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39188 (p : Pattern) (guard : d8106 p = 1) : d1909 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1909, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35118 p hg
    simpa only [d8106, d1909, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1909, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d1909, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39189 (p : Pattern) (guard : d8111 p = 1) : d1910 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35139 p hg
    simpa only [d8111, d1910, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1910, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d1910, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39190 (p : Pattern) (guard : d8112 p = 1) : d1911 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1911, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39188 p hg
    simpa only [d8112, d1911, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1911, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39189 p hg
    simpa only [d8112, d1911, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39191 (p : Pattern) (guard : d8113 p = 1) : d1912 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1912, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39187 p hg
    simpa only [d8113, d1912, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1912, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39190 p hg
    simpa only [d8113, d1912, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39192 (p : Pattern) (guard : d8106 p = 1) : d1909 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35126 p hg
    simpa only [d8106, d1909, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1909, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d1909, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39193 (p : Pattern) (guard : d8112 p = 1) : d1911 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39192 p hg
    simpa only [d8112, d1911, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1911, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39189 p hg
    simpa only [d8112, d1911, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39194 (p : Pattern) (guard : d8117 p = 1) : d278 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38691 p hg
    simpa only [d8117, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d278, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d278, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39195 (p : Pattern) (guard : d8118 p = 1) : d1913 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39193 p hg
    simpa only [d8118, d1913, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1913, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39194 p hg
    simpa only [d8118, d1913, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39196 (p : Pattern) (guard : d8119 p = 1) : d1914 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1914, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39191 p hg
    simpa only [d8119, d1914, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1914, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39195 p hg
    simpa only [d8119, d1914, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39197 (p : Pattern) (guard : d8120 p = 1) : d1915 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1915, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39171 p hg
    simpa only [d8120, d1915, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1915, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39196 p hg
    simpa only [d8120, d1915, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39198 (p : Pattern) (guard : d8094 p = 1) : d333 p ≤ (0 : Int) + d333 p := by
  omega
theorem compare39199 (p : Pattern) (guard : d8095 p = 1) : d1916 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1916, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35203 p hg
    simpa only [d8095, d1916, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1916, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39198 p hg
    simpa only [d8095, d1916, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
