/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons283
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare39760 (p : Pattern) (guard : d8118 p = 1) : d1801 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1801, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39757 p hg
    simpa only [d8118, d1801, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1801, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39759 p hg
    simpa only [d8118, d1801, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39761 (p : Pattern) (guard : d8124 p = 1) : d1808 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1808, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39760 p hg
    simpa only [d8124, d1808, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1808, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39742 p hg
    simpa only [d8124, d1808, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39762 (p : Pattern) (guard : d8130 p = 1) : d1814 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1814, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39761 p hg
    simpa only [d8130, d1814, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1814, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39744 p hg
    simpa only [d8130, d1814, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39763 (p : Pattern) (guard : d5847 p = 1) : d14 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d5843 p = 1 := by simpa only [d5847, d14, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34173 p hg
    simpa only [d5847, d14, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5847, d14, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17644 p hg
    simpa only [d5847, d14, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39764 (p : Pattern) (guard : d5854 p = 1) : d14 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39763 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d5854, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39765 (p : Pattern) (guard : d8099 p = 1) : d14 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39764 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare11458 p hg
    simpa only [d8099, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39766 (p : Pattern) (guard : d8105 p = 1) : d15 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d15, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39765 p hg
    simpa only [d8105, d15, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d15, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d15, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39767 (p : Pattern) (guard : d8111 p = 1) : d1783 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1783, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39766 p hg
    simpa only [d8111, d1783, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1783, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15328 p hg
    simpa only [d8111, d1783, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39768 (p : Pattern) (guard : d8117 p = 1) : d1815 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1815, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39767 p hg
    simpa only [d8117, d1815, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1815, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39578 p hg
    simpa only [d8117, d1815, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39769 (p : Pattern) (guard : d8123 p = 1) : d1817 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1817, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39768 p hg
    simpa only [d8123, d1817, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1817, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39749 p hg
    simpa only [d8123, d1817, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39770 (p : Pattern) (guard : d8129 p = 1) : d1820 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1820, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39769 p hg
    simpa only [d8129, d1820, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1820, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39751 p hg
    simpa only [d8129, d1820, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39771 (p : Pattern) (guard : d8135 p = 1) : d1824 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1824, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39770 p hg
    simpa only [d8135, d1824, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1824, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39753 p hg
    simpa only [d8135, d1824, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39772 (p : Pattern) (guard : d8136 p = 1) : d1825 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1825, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39762 p hg
    simpa only [d8136, d1825, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1825, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39771 p hg
    simpa only [d8136, d1825, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39773 (p : Pattern) (guard : d8142 p = 1) : d1847 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d1847, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39772 p hg
    simpa only [d8142, d1847, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d1847, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare37397 p hg
    simpa only [d8142, d1847, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39774 (p : Pattern) (guard : d8143 p = 1) : d1848 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d1848, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39756 p hg
    simpa only [d8143, d1848, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d1848, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39773 p hg
    simpa only [d8143, d1848, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39775 (p : Pattern) (guard : d8144 p = 1) : d1849 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8138 p = 1 := by simpa only [d8144, d1849, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39685 p hg
    simpa only [d8144, d1849, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8143 p = 1 := by simpa only [d8144, d1849, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39774 p hg
    simpa only [d8144, d1849, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39776 (p : Pattern) (guard : d8094 p = 1) : d358 p ≤ (0 : Int) + d358 p := by
  omega
theorem compare39777 (p : Pattern) (guard : d8095 p = 1) : d1871 p ≤ (0 : Int) + d432 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1871, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35697 p hg
    simpa only [d8095, d1871, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1871, d432, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39776 p hg
    simpa only [d8095, d1871, d432, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39778 (p : Pattern) (guard : d8089 p = 1) : d1874 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1874, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35272 p hg
    simpa only [d8089, d1874, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1874, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39140 p hg
    simpa only [d8089, d1874, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39779 (p : Pattern) (guard : d8094 p = 1) : d1875 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1875, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39778 p hg
    simpa only [d8094, d1875, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1875, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39147 p hg
    simpa only [d8094, d1875, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39780 (p : Pattern) (guard : d8100 p = 1) : d1876 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1876, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39779 p hg
    simpa only [d8100, d1876, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1876, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1876, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39781 (p : Pattern) (guard : d8101 p = 1) : d1877 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1877, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39777 p hg
    simpa only [d8101, d1877, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1877, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39780 p hg
    simpa only [d8101, d1877, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39782 (p : Pattern) (guard : d8100 p = 1) : d104 p ≤ (0 : Int) + d342 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d104, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35703 p hg
    simpa only [d8100, d104, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d104, d342, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d104, d342, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39783 (p : Pattern) (guard : d5854 p = 1) : d1874 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1874, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35366 p hg
    simpa only [d5854, d1874, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1874, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17309 p hg
    simpa only [d5854, d1874, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39784 (p : Pattern) (guard : d8099 p = 1) : d1875 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1875, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39783 p hg
    simpa only [d8099, d1875, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1875, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17309 p hg
    simpa only [d8099, d1875, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39785 (p : Pattern) (guard : d8105 p = 1) : d1876 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1876, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39784 p hg
    simpa only [d8105, d1876, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1876, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1876, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39786 (p : Pattern) (guard : d8106 p = 1) : d1878 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1878, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39782 p hg
    simpa only [d8106, d1878, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1878, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39785 p hg
    simpa only [d8106, d1878, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39787 (p : Pattern) (guard : d8107 p = 1) : d1879 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1879, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39781 p hg
    simpa only [d8107, d1879, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1879, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39786 p hg
    simpa only [d8107, d1879, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39788 (p : Pattern) (guard : d8100 p = 1) : d104 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d104, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35710 p hg
    simpa only [d8100, d104, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d104, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d104, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39789 (p : Pattern) (guard : d8106 p = 1) : d1878 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1878, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39788 p hg
    simpa only [d8106, d1878, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1878, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39321 p hg
    simpa only [d8106, d1878, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39790 (p : Pattern) (guard : d8105 p = 1) : d108 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d108, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35716 p hg
    simpa only [d8105, d108, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d108, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d108, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39791 (p : Pattern) (guard : d8111 p = 1) : d1885 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1885, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39790 p hg
    simpa only [d8111, d1885, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1885, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15424 p hg
    simpa only [d8111, d1885, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39792 (p : Pattern) (guard : d8112 p = 1) : d1886 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1886, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39789 p hg
    simpa only [d8112, d1886, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1886, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39791 p hg
    simpa only [d8112, d1886, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39793 (p : Pattern) (guard : d8113 p = 1) : d1887 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1887, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39787 p hg
    simpa only [d8113, d1887, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1887, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39792 p hg
    simpa only [d8113, d1887, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39794 (p : Pattern) (guard : d8105 p = 1) : d108 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d108, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35724 p hg
    simpa only [d8105, d108, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d108, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d108, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39795 (p : Pattern) (guard : d8111 p = 1) : d1885 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1885, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39794 p hg
    simpa only [d8111, d1885, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1885, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15424 p hg
    simpa only [d8111, d1885, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39796 (p : Pattern) (guard : d8112 p = 1) : d1886 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1886, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39344 p hg
    simpa only [d8112, d1886, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1886, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39795 p hg
    simpa only [d8112, d1886, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39797 (p : Pattern) (guard : d8117 p = 1) : d1888 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1888, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39213 p hg
    simpa only [d8117, d1888, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1888, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1888, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39798 (p : Pattern) (guard : d8118 p = 1) : d1889 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1889, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39796 p hg
    simpa only [d8118, d1889, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1889, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39797 p hg
    simpa only [d8118, d1889, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39799 (p : Pattern) (guard : d8119 p = 1) : d1890 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1890, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39793 p hg
    simpa only [d8119, d1890, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1890, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39798 p hg
    simpa only [d8119, d1890, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39800 (p : Pattern) (guard : d8106 p = 1) : d1900 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1900, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39297 p hg
    simpa only [d8106, d1900, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1900, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39261 p hg
    simpa only [d8106, d1900, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39801 (p : Pattern) (guard : d8111 p = 1) : d1907 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1907, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35749 p hg
    simpa only [d8111, d1907, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1907, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15433 p hg
    simpa only [d8111, d1907, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39802 (p : Pattern) (guard : d8112 p = 1) : d1908 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1908, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39800 p hg
    simpa only [d8112, d1908, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1908, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39801 p hg
    simpa only [d8112, d1908, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39803 (p : Pattern) (guard : d8111 p = 1) : d1909 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1909, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35705 p hg
    simpa only [d8111, d1909, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1909, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d1909, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39804 (p : Pattern) (guard : d8117 p = 1) : d1911 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1911, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39803 p hg
    simpa only [d8117, d1911, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1911, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39337 p hg
    simpa only [d8117, d1911, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39805 (p : Pattern) (guard : d8118 p = 1) : d1912 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1912, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39802 p hg
    simpa only [d8118, d1912, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1912, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39804 p hg
    simpa only [d8118, d1912, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39806 (p : Pattern) (guard : d8124 p = 1) : d1914 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1914, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39805 p hg
    simpa only [d8124, d1914, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1914, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39340 p hg
    simpa only [d8124, d1914, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39807 (p : Pattern) (guard : d8125 p = 1) : d1915 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1915, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39799 p hg
    simpa only [d8125, d1915, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1915, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39806 p hg
    simpa only [d8125, d1915, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39808 (p : Pattern) (guard : d8099 p = 1) : d333 p ≤ (0 : Int) + d333 p := by
  omega
theorem compare39809 (p : Pattern) (guard : d8100 p = 1) : d1916 p ≤ (0 : Int) + d334 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1916, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35747 p hg
    simpa only [d8100, d1916, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1916, d334, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39808 p hg
    simpa only [d8100, d1916, d334, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39810 (p : Pattern) (guard : d5854 p = 1) : d1874 p ≤ (0 : Int) + d330 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1874, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35733 p hg
    simpa only [d5854, d1874, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1874, d330, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17309 p hg
    simpa only [d5854, d1874, d330, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39811 (p : Pattern) (guard : d8099 p = 1) : d1875 p ≤ (0 : Int) + d335 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1875, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39810 p hg
    simpa only [d8099, d1875, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1875, d335, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17309 p hg
    simpa only [d8099, d1875, d335, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39812 (p : Pattern) (guard : d8105 p = 1) : d1876 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1876, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39811 p hg
    simpa only [d8105, d1876, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1876, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1876, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39813 (p : Pattern) (guard : d8106 p = 1) : d1917 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1917, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39809 p hg
    simpa only [d8106, d1917, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1917, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39812 p hg
    simpa only [d8106, d1917, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39814 (p : Pattern) (guard : d8105 p = 1) : d117 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d117, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35754 p hg
    simpa only [d8105, d117, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d117, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d117, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39815 (p : Pattern) (guard : d8111 p = 1) : d1923 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1923, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39814 p hg
    simpa only [d8111, d1923, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1923, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15448 p hg
    simpa only [d8111, d1923, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39816 (p : Pattern) (guard : d8112 p = 1) : d1924 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1924, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39813 p hg
    simpa only [d8112, d1924, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1924, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39815 p hg
    simpa only [d8112, d1924, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39817 (p : Pattern) (guard : d8105 p = 1) : d108 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d108, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35761 p hg
    simpa only [d8105, d108, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d108, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d108, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39818 (p : Pattern) (guard : d8111 p = 1) : d1885 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1885, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39817 p hg
    simpa only [d8111, d1885, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1885, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15424 p hg
    simpa only [d8111, d1885, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39819 (p : Pattern) (guard : d8117 p = 1) : d2088 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2088, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39818 p hg
    simpa only [d8117, d2088, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2088, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35764 p hg
    simpa only [d8117, d2088, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39820 (p : Pattern) (guard : d8118 p = 1) : d2089 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2089, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39816 p hg
    simpa only [d8118, d2089, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2089, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39819 p hg
    simpa only [d8118, d2089, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39821 (p : Pattern) (guard : d8117 p = 1) : d2088 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2088, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39791 p hg
    simpa only [d8117, d2088, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2088, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35767 p hg
    simpa only [d8117, d2088, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39822 (p : Pattern) (guard : d8123 p = 1) : d2090 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2090, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39821 p hg
    simpa only [d8123, d2090, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2090, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d2090, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39823 (p : Pattern) (guard : d8124 p = 1) : d2091 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2091, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39820 p hg
    simpa only [d8124, d2091, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2091, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39822 p hg
    simpa only [d8124, d2091, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39824 (p : Pattern) (guard : d8105 p = 1) : d104 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d104, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35774 p hg
    simpa only [d8105, d104, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d104, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d104, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39825 (p : Pattern) (guard : d8111 p = 1) : d1907 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1907, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39824 p hg
    simpa only [d8111, d1907, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1907, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15433 p hg
    simpa only [d8111, d1907, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39826 (p : Pattern) (guard : d8117 p = 1) : d1931 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1931, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39825 p hg
    simpa only [d8117, d1931, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1931, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39355 p hg
    simpa only [d8117, d1931, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39827 (p : Pattern) (guard : d0 p = 1) : d2092 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39828 (p : Pattern) (guard : d8123 p = 1) : d2093 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2093, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39826 p hg
    simpa only [d8123, d2093, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2093, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39827 p hg
    simpa only [d8123, d2093, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39829 (p : Pattern) (guard : d0 p = 1) : d2094 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39830 (p : Pattern) (guard : d8129 p = 1) : d2095 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2095, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39828 p hg
    simpa only [d8129, d2095, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2095, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39829 p hg
    simpa only [d8129, d2095, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39831 (p : Pattern) (guard : d8130 p = 1) : d2096 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2096, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39823 p hg
    simpa only [d8130, d2096, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2096, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39830 p hg
    simpa only [d8130, d2096, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39832 (p : Pattern) (guard : d8131 p = 1) : d2097 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d2097, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39807 p hg
    simpa only [d8131, d2097, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d2097, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39831 p hg
    simpa only [d8131, d2097, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39833 (p : Pattern) (guard : d8106 p = 1) : d1944 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1944, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39343 p hg
    simpa only [d8106, d1944, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1944, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39365 p hg
    simpa only [d8106, d1944, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39834 (p : Pattern) (guard : d8111 p = 1) : d1953 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1953, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39824 p hg
    simpa only [d8111, d1953, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1953, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15467 p hg
    simpa only [d8111, d1953, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39835 (p : Pattern) (guard : d8112 p = 1) : d1954 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1954, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39833 p hg
    simpa only [d8112, d1954, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1954, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39834 p hg
    simpa only [d8112, d1954, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39836 (p : Pattern) (guard : d8111 p = 1) : d1959 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1959, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35749 p hg
    simpa only [d8111, d1959, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1959, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15470 p hg
    simpa only [d8111, d1959, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39837 (p : Pattern) (guard : d8117 p = 1) : d1969 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1969, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39836 p hg
    simpa only [d8117, d1969, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1969, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39370 p hg
    simpa only [d8117, d1969, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39838 (p : Pattern) (guard : d8118 p = 1) : d1970 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1970, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39835 p hg
    simpa only [d8118, d1970, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1970, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39837 p hg
    simpa only [d8118, d1970, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39839 (p : Pattern) (guard : d8111 p = 1) : d1959 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1959, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35705 p hg
    simpa only [d8111, d1959, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1959, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15470 p hg
    simpa only [d8111, d1959, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39840 (p : Pattern) (guard : d8117 p = 1) : d1969 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1969, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39839 p hg
    simpa only [d8117, d1969, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1969, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39370 p hg
    simpa only [d8117, d1969, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39841 (p : Pattern) (guard : d8123 p = 1) : d1971 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1971, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39840 p hg
    simpa only [d8123, d1971, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1971, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39373 p hg
    simpa only [d8123, d1971, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39842 (p : Pattern) (guard : d8124 p = 1) : d1972 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1972, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39838 p hg
    simpa only [d8124, d1972, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1972, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39841 p hg
    simpa only [d8124, d1972, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39843 (p : Pattern) (guard : d8130 p = 1) : d1978 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1978, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39842 p hg
    simpa only [d8130, d1978, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1978, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39380 p hg
    simpa only [d8130, d1978, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39844 (p : Pattern) (guard : d8105 p = 1) : d104 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d104, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35795 p hg
    simpa only [d8105, d104, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d104, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d104, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39845 (p : Pattern) (guard : d8111 p = 1) : d1953 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1953, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39844 p hg
    simpa only [d8111, d1953, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1953, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15467 p hg
    simpa only [d8111, d1953, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39846 (p : Pattern) (guard : d0 p = 1) : d1973 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39847 (p : Pattern) (guard : d8117 p = 1) : d1979 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1979, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39845 p hg
    simpa only [d8117, d1979, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1979, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39846 p hg
    simpa only [d8117, d1979, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39848 (p : Pattern) (guard : d0 p = 1) : d2098 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39849 (p : Pattern) (guard : d8123 p = 1) : d2099 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2099, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39847 p hg
    simpa only [d8123, d2099, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2099, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39848 p hg
    simpa only [d8123, d2099, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39850 (p : Pattern) (guard : d0 p = 1) : d2100 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39851 (p : Pattern) (guard : d8129 p = 1) : d2101 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2101, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39849 p hg
    simpa only [d8129, d2101, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2101, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39850 p hg
    simpa only [d8129, d2101, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39852 (p : Pattern) (guard : d8135 p = 1) : d2102 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2102, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39851 p hg
    simpa only [d8135, d2102, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2102, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39389 p hg
    simpa only [d8135, d2102, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39853 (p : Pattern) (guard : d8136 p = 1) : d2103 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2103, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39843 p hg
    simpa only [d8136, d2103, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2103, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39852 p hg
    simpa only [d8136, d2103, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39854 (p : Pattern) (guard : d8137 p = 1) : d2104 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d2104, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39832 p hg
    simpa only [d8137, d2104, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d2104, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39853 p hg
    simpa only [d8137, d2104, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39855 (p : Pattern) (guard : d8106 p = 1) : d1944 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1944, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39788 p hg
    simpa only [d8106, d1944, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1944, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39365 p hg
    simpa only [d8106, d1944, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39856 (p : Pattern) (guard : d8112 p = 1) : d1954 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1954, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39855 p hg
    simpa only [d8112, d1954, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1954, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39845 p hg
    simpa only [d8112, d1954, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39857 (p : Pattern) (guard : d8111 p = 1) : d1959 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1959, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39824 p hg
    simpa only [d8111, d1959, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1959, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15470 p hg
    simpa only [d8111, d1959, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39858 (p : Pattern) (guard : d8117 p = 1) : d1969 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1969, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39857 p hg
    simpa only [d8117, d1969, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1969, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39370 p hg
    simpa only [d8117, d1969, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39859 (p : Pattern) (guard : d8118 p = 1) : d1970 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1970, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39856 p hg
    simpa only [d8118, d1970, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1970, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39858 p hg
    simpa only [d8118, d1970, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39860 (p : Pattern) (guard : d8123 p = 1) : d1971 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1971, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39837 p hg
    simpa only [d8123, d1971, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1971, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39373 p hg
    simpa only [d8123, d1971, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39861 (p : Pattern) (guard : d8124 p = 1) : d1972 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1972, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39859 p hg
    simpa only [d8124, d1972, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1972, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39860 p hg
    simpa only [d8124, d1972, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39862 (p : Pattern) (guard : d8117 p = 1) : d1975 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1975, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39270 p hg
    simpa only [d8117, d1975, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1975, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39377 p hg
    simpa only [d8117, d1975, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39863 (p : Pattern) (guard : d8123 p = 1) : d1976 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1976, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39862 p hg
    simpa only [d8123, d1976, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1976, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1976, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39864 (p : Pattern) (guard : d8129 p = 1) : d1977 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1977, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39863 p hg
    simpa only [d8129, d1977, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1977, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1977, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39865 (p : Pattern) (guard : d8130 p = 1) : d1978 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1978, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39861 p hg
    simpa only [d8130, d1978, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1978, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39864 p hg
    simpa only [d8130, d1978, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39866 (p : Pattern) (guard : d8105 p = 1) : d104 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d104, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35818 p hg
    simpa only [d8105, d104, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d104, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d104, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39867 (p : Pattern) (guard : d8111 p = 1) : d1953 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1953, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39866 p hg
    simpa only [d8111, d1953, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1953, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15467 p hg
    simpa only [d8111, d1953, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39868 (p : Pattern) (guard : d0 p = 1) : d1973 p ≤ (0 : Int) + d370 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39869 (p : Pattern) (guard : d8117 p = 1) : d1979 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1979, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39867 p hg
    simpa only [d8117, d1979, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1979, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39868 p hg
    simpa only [d8117, d1979, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39870 (p : Pattern) (guard : d0 p = 1) : d2098 p ≤ (0 : Int) + d374 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39871 (p : Pattern) (guard : d8123 p = 1) : d2099 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2099, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39869 p hg
    simpa only [d8123, d2099, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2099, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39870 p hg
    simpa only [d8123, d2099, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39872 (p : Pattern) (guard : d8129 p = 1) : d2101 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2101, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39871 p hg
    simpa only [d8129, d2101, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2101, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39850 p hg
    simpa only [d8129, d2101, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39873 (p : Pattern) (guard : d8135 p = 1) : d2102 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d2102, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39872 p hg
    simpa only [d8135, d2102, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d2102, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39389 p hg
    simpa only [d8135, d2102, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39874 (p : Pattern) (guard : d8136 p = 1) : d2103 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d2103, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39865 p hg
    simpa only [d8136, d2103, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d2103, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39873 p hg
    simpa only [d8136, d2103, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39875 (p : Pattern) (guard : d8123 p = 1) : d1991 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1991, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39797 p hg
    simpa only [d8123, d1991, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1991, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1991, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39876 (p : Pattern) (guard : d8129 p = 1) : d1992 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1992, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39875 p hg
    simpa only [d8129, d1992, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1992, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1992, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39877 (p : Pattern) (guard : d8135 p = 1) : d1993 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1993, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39876 p hg
    simpa only [d8135, d1993, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1993, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d1993, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39878 (p : Pattern) (guard : d8141 p = 1) : d1994 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8135 p = 1 := by simpa only [d8141, d1994, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39877 p hg
    simpa only [d8141, d1994, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8141, d1994, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8141, d1994, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39879 (p : Pattern) (guard : d8142 p = 1) : d2105 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8136 p = 1 := by simpa only [d8142, d2105, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39874 p hg
    simpa only [d8142, d2105, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8141 p = 1 := by simpa only [d8142, d2105, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39878 p hg
    simpa only [d8142, d2105, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39880 (p : Pattern) (guard : d8143 p = 1) : d2106 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8137 p = 1 := by simpa only [d8143, d2106, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39854 p hg
    simpa only [d8143, d2106, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8142 p = 1 := by simpa only [d8143, d2106, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39879 p hg
    simpa only [d8143, d2106, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39881 (p : Pattern) (guard : d5854 p = 1) : d1941 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1941, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35366 p hg
    simpa only [d5854, d1941, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1941, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17386 p hg
    simpa only [d5854, d1941, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39882 (p : Pattern) (guard : d8099 p = 1) : d1942 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1942, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39881 p hg
    simpa only [d8099, d1942, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1942, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17386 p hg
    simpa only [d8099, d1942, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39883 (p : Pattern) (guard : d8105 p = 1) : d1943 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1943, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39882 p hg
    simpa only [d8105, d1943, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1943, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1943, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39884 (p : Pattern) (guard : d8106 p = 1) : d1944 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1944, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39782 p hg
    simpa only [d8106, d1944, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1944, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39883 p hg
    simpa only [d8106, d1944, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39885 (p : Pattern) (guard : d8111 p = 1) : d1944 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1944, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39866 p hg
    simpa only [d8111, d1944, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1944, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15465 p hg
    simpa only [d8111, d1944, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39886 (p : Pattern) (guard : d8112 p = 1) : d1944 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39884 p hg
    simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39885 p hg
    simpa only [d8112, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39887 (p : Pattern) (guard : d8111 p = 1) : d2110 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d2110, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39844 p hg
    simpa only [d8111, d2110, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d2110, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15603 p hg
    simpa only [d8111, d2110, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39888 (p : Pattern) (guard : d0 p = 1) : d1968 p ≤ (0 : Int) + d373 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39889 (p : Pattern) (guard : d8117 p = 1) : d2111 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2111, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39887 p hg
    simpa only [d8117, d2111, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2111, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39888 p hg
    simpa only [d8117, d2111, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39890 (p : Pattern) (guard : d8118 p = 1) : d2112 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d2112, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39886 p hg
    simpa only [d8118, d2112, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d2112, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39889 p hg
    simpa only [d8118, d2112, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39891 (p : Pattern) (guard : d8117 p = 1) : d2113 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2113, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39834 p hg
    simpa only [d8117, d2113, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2113, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39370 p hg
    simpa only [d8117, d2113, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39892 (p : Pattern) (guard : d8123 p = 1) : d2114 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2114, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39891 p hg
    simpa only [d8123, d2114, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2114, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39373 p hg
    simpa only [d8123, d2114, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39893 (p : Pattern) (guard : d8124 p = 1) : d2115 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d2115, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39890 p hg
    simpa only [d8124, d2115, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d2115, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39892 p hg
    simpa only [d8124, d2115, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39894 (p : Pattern) (guard : d0 p = 1) : d2116 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39895 (p : Pattern) (guard : d8117 p = 1) : d2117 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d2117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39304 p hg
    simpa only [d8117, d2117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d2117, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39894 p hg
    simpa only [d8117, d2117, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39896 (p : Pattern) (guard : d8123 p = 1) : d2118 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d2118, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39895 p hg
    simpa only [d8123, d2118, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d2118, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39827 p hg
    simpa only [d8123, d2118, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39897 (p : Pattern) (guard : d0 p = 1) : d2121 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39898 (p : Pattern) (guard : d8129 p = 1) : d2122 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d2122, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39896 p hg
    simpa only [d8129, d2122, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d2122, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39897 p hg
    simpa only [d8129, d2122, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39899 (p : Pattern) (guard : d8130 p = 1) : d2123 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d2123, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39893 p hg
    simpa only [d8130, d2123, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d2123, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39898 p hg
    simpa only [d8130, d2123, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
