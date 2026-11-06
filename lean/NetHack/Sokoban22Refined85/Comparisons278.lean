/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons277
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare38920 (p : Pattern) (guard : d8105 p = 1) : d1746 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38919 p hg
    simpa only [d8105, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1746, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1746, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38921 (p : Pattern) (guard : d8106 p = 1) : d1747 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1747, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38917 p hg
    simpa only [d8106, d1747, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1747, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38920 p hg
    simpa only [d8106, d1747, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38922 (p : Pattern) (guard : d8107 p = 1) : d1841 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1841, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38916 p hg
    simpa only [d8107, d1841, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1841, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38921 p hg
    simpa only [d8107, d1841, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38923 (p : Pattern) (guard : d8100 p = 1) : d19 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d19, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34888 p hg
    simpa only [d8100, d19, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d19, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d19, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38924 (p : Pattern) (guard : d8106 p = 1) : d1698 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1698, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38923 p hg
    simpa only [d8106, d1698, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1698, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38892 p hg
    simpa only [d8106, d1698, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38925 (p : Pattern) (guard : d8111 p = 1) : d1706 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34598 p hg
    simpa only [d8111, d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1706, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15276 p hg
    simpa only [d8111, d1706, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38926 (p : Pattern) (guard : d8112 p = 1) : d1749 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1749, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38924 p hg
    simpa only [d8112, d1749, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1749, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38925 p hg
    simpa only [d8112, d1749, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38927 (p : Pattern) (guard : d8113 p = 1) : d1842 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1842, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38922 p hg
    simpa only [d8113, d1842, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1842, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38926 p hg
    simpa only [d8113, d1842, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38928 (p : Pattern) (guard : d8112 p = 1) : d1755 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1755, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38893 p hg
    simpa only [d8112, d1755, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1755, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38748 p hg
    simpa only [d8112, d1755, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38929 (p : Pattern) (guard : d8118 p = 1) : d1758 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1758, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38928 p hg
    simpa only [d8118, d1758, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1758, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38751 p hg
    simpa only [d8118, d1758, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38930 (p : Pattern) (guard : d8119 p = 1) : d1843 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1843, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38927 p hg
    simpa only [d8119, d1843, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1843, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38929 p hg
    simpa only [d8119, d1843, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38931 (p : Pattern) (guard : d8111 p = 1) : d1760 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8111, d1760, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1760, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d1760, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38932 (p : Pattern) (guard : d8112 p = 1) : d1761 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38903 p hg
    simpa only [d8112, d1761, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1761, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38931 p hg
    simpa only [d8112, d1761, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38933 (p : Pattern) (guard : d0 p = 1) : d527 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38934 (p : Pattern) (guard : d8117 p = 1) : d1762 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38906 p hg
    simpa only [d8117, d1762, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1762, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38933 p hg
    simpa only [d8117, d1762, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38935 (p : Pattern) (guard : d8118 p = 1) : d1763 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38932 p hg
    simpa only [d8118, d1763, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1763, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38934 p hg
    simpa only [d8118, d1763, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38936 (p : Pattern) (guard : d0 p = 1) : d277 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38937 (p : Pattern) (guard : d8117 p = 1) : d1764 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38906 p hg
    simpa only [d8117, d1764, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1764, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38936 p hg
    simpa only [d8117, d1764, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38938 (p : Pattern) (guard : d0 p = 1) : d539 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38939 (p : Pattern) (guard : d8123 p = 1) : d1765 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38937 p hg
    simpa only [d8123, d1765, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1765, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38938 p hg
    simpa only [d8123, d1765, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38940 (p : Pattern) (guard : d8124 p = 1) : d1766 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38935 p hg
    simpa only [d8124, d1766, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1766, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38939 p hg
    simpa only [d8124, d1766, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38941 (p : Pattern) (guard : d8125 p = 1) : d1844 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1844, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38930 p hg
    simpa only [d8125, d1844, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1844, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38940 p hg
    simpa only [d8125, d1844, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38942 (p : Pattern) (guard : d8126 p = 1) : d1866 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1866, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38914 p hg
    simpa only [d8126, d1866, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1866, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38941 p hg
    simpa only [d8126, d1866, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38943 (p : Pattern) (guard : d8089 p = 1) : d1771 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34339 p hg
    simpa only [d8089, d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1771, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38701 p hg
    simpa only [d8089, d1771, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38944 (p : Pattern) (guard : d5854 p = 1) : d1770 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38701 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17200 p hg
    simpa only [d5854, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38945 (p : Pattern) (guard : d8094 p = 1) : d1772 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38943 p hg
    simpa only [d8094, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1772, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38944 p hg
    simpa only [d8094, d1772, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38946 (p : Pattern) (guard : d8100 p = 1) : d1773 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38945 p hg
    simpa only [d8100, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1773, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1773, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38947 (p : Pattern) (guard : d8101 p = 1) : d1774 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1774, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34967 p hg
    simpa only [d8101, d1774, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1774, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38946 p hg
    simpa only [d8101, d1774, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38948 (p : Pattern) (guard : d5854 p = 1) : d1777 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34416 p hg
    simpa only [d5854, d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1777, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17207 p hg
    simpa only [d5854, d1777, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38949 (p : Pattern) (guard : d0 p = 1) : d1780 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38950 (p : Pattern) (guard : d8099 p = 1) : d1781 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38948 p hg
    simpa only [d8099, d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1781, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38949 p hg
    simpa only [d8099, d1781, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38951 (p : Pattern) (guard : d8105 p = 1) : d1782 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38950 p hg
    simpa only [d8105, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1782, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1782, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38952 (p : Pattern) (guard : d8106 p = 1) : d1783 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34696 p hg
    simpa only [d8106, d1783, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1783, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38951 p hg
    simpa only [d8106, d1783, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38953 (p : Pattern) (guard : d8107 p = 1) : d1784 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1784, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38947 p hg
    simpa only [d8107, d1784, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1784, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38952 p hg
    simpa only [d8107, d1784, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38954 (p : Pattern) (guard : d0 p = 1) : d1787 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38955 (p : Pattern) (guard : d8099 p = 1) : d1788 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38948 p hg
    simpa only [d8099, d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1788, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38954 p hg
    simpa only [d8099, d1788, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38956 (p : Pattern) (guard : d8105 p = 1) : d1789 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38955 p hg
    simpa only [d8105, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1789, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1789, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38957 (p : Pattern) (guard : d8106 p = 1) : d1790 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34696 p hg
    simpa only [d8106, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38956 p hg
    simpa only [d8106, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38958 (p : Pattern) (guard : d8111 p = 1) : d1799 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34700 p hg
    simpa only [d8111, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1799, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15333 p hg
    simpa only [d8111, d1799, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38959 (p : Pattern) (guard : d8112 p = 1) : d1800 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38957 p hg
    simpa only [d8112, d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38958 p hg
    simpa only [d8112, d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38960 (p : Pattern) (guard : d8113 p = 1) : d1801 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1801, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38953 p hg
    simpa only [d8113, d1801, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1801, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38959 p hg
    simpa only [d8113, d1801, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38961 (p : Pattern) (guard : d8117 p = 1) : d1806 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38745 p hg
    simpa only [d8117, d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1806, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1806, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38962 (p : Pattern) (guard : d8118 p = 1) : d1807 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38959 p hg
    simpa only [d8118, d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38961 p hg
    simpa only [d8118, d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38963 (p : Pattern) (guard : d8119 p = 1) : d1808 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1808, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38960 p hg
    simpa only [d8119, d1808, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1808, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38962 p hg
    simpa only [d8119, d1808, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38964 (p : Pattern) (guard : d8111 p = 1) : d1810 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34711 p hg
    simpa only [d8111, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1810, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15283 p hg
    simpa only [d8111, d1810, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38965 (p : Pattern) (guard : d8112 p = 1) : d1811 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38743 p hg
    simpa only [d8112, d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1811, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38964 p hg
    simpa only [d8112, d1811, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38966 (p : Pattern) (guard : d8118 p = 1) : d1812 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38965 p hg
    simpa only [d8118, d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1812, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38751 p hg
    simpa only [d8118, d1812, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38967 (p : Pattern) (guard : d8124 p = 1) : d1813 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38966 p hg
    simpa only [d8124, d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38968 (p : Pattern) (guard : d8125 p = 1) : d1814 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1814, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38963 p hg
    simpa only [d8125, d1814, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1814, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38967 p hg
    simpa only [d8125, d1814, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38969 (p : Pattern) (guard : d8106 p = 1) : d1783 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1783, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35389 p hg
    simpa only [d8106, d1783, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1783, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38951 p hg
    simpa only [d8106, d1783, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38970 (p : Pattern) (guard : d8111 p = 1) : d1809 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8111, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1809, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15281 p hg
    simpa only [d8111, d1809, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38971 (p : Pattern) (guard : d8112 p = 1) : d1815 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1815, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38969 p hg
    simpa only [d8112, d1815, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1815, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38970 p hg
    simpa only [d8112, d1815, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38972 (p : Pattern) (guard : d0 p = 1) : d1805 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38973 (p : Pattern) (guard : d8117 p = 1) : d1816 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38958 p hg
    simpa only [d8117, d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1816, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38972 p hg
    simpa only [d8117, d1816, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38974 (p : Pattern) (guard : d8118 p = 1) : d1817 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1817, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38971 p hg
    simpa only [d8118, d1817, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1817, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38973 p hg
    simpa only [d8118, d1817, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38975 (p : Pattern) (guard : d0 p = 1) : d1754 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38976 (p : Pattern) (guard : d8117 p = 1) : d1818 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38958 p hg
    simpa only [d8117, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1818, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38975 p hg
    simpa only [d8117, d1818, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38977 (p : Pattern) (guard : d0 p = 1) : d1757 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare38978 (p : Pattern) (guard : d8123 p = 1) : d1819 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38976 p hg
    simpa only [d8123, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1819, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38977 p hg
    simpa only [d8123, d1819, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38979 (p : Pattern) (guard : d8124 p = 1) : d1820 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1820, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38974 p hg
    simpa only [d8124, d1820, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1820, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38978 p hg
    simpa only [d8124, d1820, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38980 (p : Pattern) (guard : d8117 p = 1) : d1821 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38964 p hg
    simpa only [d8117, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1821, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1821, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38981 (p : Pattern) (guard : d8123 p = 1) : d1822 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38980 p hg
    simpa only [d8123, d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1822, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1822, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38982 (p : Pattern) (guard : d8129 p = 1) : d1823 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38981 p hg
    simpa only [d8129, d1823, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1823, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1823, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38983 (p : Pattern) (guard : d8130 p = 1) : d1824 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1824, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38979 p hg
    simpa only [d8130, d1824, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1824, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38982 p hg
    simpa only [d8130, d1824, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38984 (p : Pattern) (guard : d8131 p = 1) : d1825 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1825, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38968 p hg
    simpa only [d8131, d1825, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1825, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38983 p hg
    simpa only [d8131, d1825, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38985 (p : Pattern) (guard : d8132 p = 1) : d1867 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1867, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38942 p hg
    simpa only [d8132, d1867, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1867, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38984 p hg
    simpa only [d8132, d1867, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38986 (p : Pattern) (guard : d8101 p = 1) : d1774 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1774, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35384 p hg
    simpa only [d8101, d1774, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1774, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38946 p hg
    simpa only [d8101, d1774, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38987 (p : Pattern) (guard : d8107 p = 1) : d1784 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1784, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38986 p hg
    simpa only [d8107, d1784, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1784, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38969 p hg
    simpa only [d8107, d1784, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38988 (p : Pattern) (guard : d8113 p = 1) : d1801 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1801, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38987 p hg
    simpa only [d8113, d1801, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1801, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38959 p hg
    simpa only [d8113, d1801, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38989 (p : Pattern) (guard : d8119 p = 1) : d1808 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1808, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38988 p hg
    simpa only [d8119, d1808, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1808, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38962 p hg
    simpa only [d8119, d1808, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38990 (p : Pattern) (guard : d8125 p = 1) : d1814 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1814, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38989 p hg
    simpa only [d8125, d1814, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1814, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38967 p hg
    simpa only [d8125, d1814, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38991 (p : Pattern) (guard : d8106 p = 1) : d1783 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1783, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35414 p hg
    simpa only [d8106, d1783, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1783, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38951 p hg
    simpa only [d8106, d1783, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38992 (p : Pattern) (guard : d8112 p = 1) : d1815 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1815, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38991 p hg
    simpa only [d8112, d1815, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1815, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38970 p hg
    simpa only [d8112, d1815, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38993 (p : Pattern) (guard : d8118 p = 1) : d1817 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1817, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38992 p hg
    simpa only [d8118, d1817, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1817, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38973 p hg
    simpa only [d8118, d1817, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38994 (p : Pattern) (guard : d8124 p = 1) : d1820 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1820, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38993 p hg
    simpa only [d8124, d1820, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1820, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38978 p hg
    simpa only [d8124, d1820, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38995 (p : Pattern) (guard : d8130 p = 1) : d1824 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1824, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38994 p hg
    simpa only [d8130, d1824, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1824, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38982 p hg
    simpa only [d8130, d1824, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38996 (p : Pattern) (guard : d8131 p = 1) : d1825 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1825, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38990 p hg
    simpa only [d8131, d1825, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1825, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38995 p hg
    simpa only [d8131, d1825, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38997 (p : Pattern) (guard : d8137 p = 1) : d1847 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1847, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38996 p hg
    simpa only [d8137, d1847, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1847, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d1847, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38998 (p : Pattern) (guard : d8138 p = 1) : d1868 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1868, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38985 p hg
    simpa only [d8138, d1868, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1868, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38997 p hg
    simpa only [d8138, d1868, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare38999 (p : Pattern) (guard : d8139 p = 1) : d1869 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d1869, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38882 p hg
    simpa only [d8139, d1869, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d1869, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38998 p hg
    simpa only [d8139, d1869, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39000 (p : Pattern) (guard : d8140 p = 1) : d1870 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d1870, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38775 p hg
    simpa only [d8140, d1870, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d1870, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38999 p hg
    simpa only [d8140, d1870, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39001 (p : Pattern) (guard : d8086 p = 1) : d321 p ≤ (0 : Int) + d321 p := by
  omega
theorem compare39002 (p : Pattern) (guard : d8087 p = 1) : d1682 p ≤ (0 : Int) + d322 p := by
  cases selected : p 204 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8087, d1682, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34323 p hg
    simpa only [d8087, d1682, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8086 p = 1 := by simpa only [d8087, d1682, d322, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39001 p hg
    simpa only [d8087, d1682, d322, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39003 (p : Pattern) (guard : d8086 p = 1) : d1686 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8086, d1686, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38338 p hg
    simpa only [d8086, d1686, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8085 p = 1 := by simpa only [d8086, d1686, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38346 p hg
    simpa only [d8086, d1686, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39004 (p : Pattern) (guard : d8091 p = 1) : d1687 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d1687, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39003 p hg
    simpa only [d8091, d1687, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d1687, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34344 p hg
    simpa only [d8091, d1687, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39005 (p : Pattern) (guard : d8092 p = 1) : d1688 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d1688, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39002 p hg
    simpa only [d8092, d1688, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d1688, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39004 p hg
    simpa only [d8092, d1688, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39006 (p : Pattern) (guard : d8097 p = 1) : d1691 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1691, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39005 p hg
    simpa only [d8097, d1691, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1691, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38811 p hg
    simpa only [d8097, d1691, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39007 (p : Pattern) (guard : d8102 p = 1) : d1699 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1699, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38786 p hg
    simpa only [d8102, d1699, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1699, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38816 p hg
    simpa only [d8102, d1699, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39008 (p : Pattern) (guard : d8103 p = 1) : d1700 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1700, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39006 p hg
    simpa only [d8103, d1700, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1700, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39007 p hg
    simpa only [d8103, d1700, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39009 (p : Pattern) (guard : d8107 p = 1) : d1707 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1707, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38445 p hg
    simpa only [d8107, d1707, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1707, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1707, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39010 (p : Pattern) (guard : d8108 p = 1) : d1708 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1708, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38790 p hg
    simpa only [d8108, d1708, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1708, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39009 p hg
    simpa only [d8108, d1708, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39011 (p : Pattern) (guard : d8109 p = 1) : d1709 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1709, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39008 p hg
    simpa only [d8109, d1709, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1709, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39010 p hg
    simpa only [d8109, d1709, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39012 (p : Pattern) (guard : d8096 p = 1) : d1719 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1719, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38596 p hg
    simpa only [d8096, d1719, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1719, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38527 p hg
    simpa only [d8096, d1719, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39013 (p : Pattern) (guard : d8102 p = 1) : d1727 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1727, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39012 p hg
    simpa only [d8102, d1727, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1727, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38826 p hg
    simpa only [d8102, d1727, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39014 (p : Pattern) (guard : d8101 p = 1) : d1731 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1731, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34781 p hg
    simpa only [d8101, d1731, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1731, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38457 p hg
    simpa only [d8101, d1731, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39015 (p : Pattern) (guard : d8107 p = 1) : d1733 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1733, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39014 p hg
    simpa only [d8107, d1733, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1733, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38656 p hg
    simpa only [d8107, d1733, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39016 (p : Pattern) (guard : d8108 p = 1) : d1734 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1734, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39013 p hg
    simpa only [d8108, d1734, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1734, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39015 p hg
    simpa only [d8108, d1734, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39017 (p : Pattern) (guard : d8101 p = 1) : d1735 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1735, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34752 p hg
    simpa only [d8101, d1735, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1735, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d1735, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39018 (p : Pattern) (guard : d8107 p = 1) : d1736 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1736, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39017 p hg
    simpa only [d8107, d1736, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1736, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38656 p hg
    simpa only [d8107, d1736, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39019 (p : Pattern) (guard : d8113 p = 1) : d1737 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1737, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39018 p hg
    simpa only [d8113, d1737, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1737, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38661 p hg
    simpa only [d8113, d1737, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39020 (p : Pattern) (guard : d8114 p = 1) : d1738 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1738, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39016 p hg
    simpa only [d8114, d1738, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1738, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39019 p hg
    simpa only [d8114, d1738, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39021 (p : Pattern) (guard : d8115 p = 1) : d1739 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1739, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39011 p hg
    simpa only [d8115, d1739, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1739, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39020 p hg
    simpa only [d8115, d1739, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39022 (p : Pattern) (guard : d8090 p = 1) : d335 p ≤ (0 : Int) + d335 p := by
  omega
theorem compare39023 (p : Pattern) (guard : d8091 p = 1) : d1740 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8086 p = 1 := by simpa only [d8091, d1740, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34965 p hg
    simpa only [d8091, d1740, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8090 p = 1 := by simpa only [d8091, d1740, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39022 p hg
    simpa only [d8091, d1740, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39024 (p : Pattern) (guard : d8085 p = 1) : d1685 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1685, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34413 p hg
    simpa only [d8085, d1685, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1685, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38345 p hg
    simpa only [d8085, d1685, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39025 (p : Pattern) (guard : d8090 p = 1) : d1686 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1686, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39024 p hg
    simpa only [d8090, d1686, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1686, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38632 p hg
    simpa only [d8090, d1686, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39026 (p : Pattern) (guard : d8095 p = 1) : d1687 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1687, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39025 p hg
    simpa only [d8095, d1687, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1687, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1687, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39027 (p : Pattern) (guard : d8096 p = 1) : d1741 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1741, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39023 p hg
    simpa only [d8096, d1741, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1741, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39026 p hg
    simpa only [d8096, d1741, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39028 (p : Pattern) (guard : d8095 p = 1) : d32 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d32, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34970 p hg
    simpa only [d8095, d32, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d32, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d32, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39029 (p : Pattern) (guard : d8101 p = 1) : d1747 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1747, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39028 p hg
    simpa only [d8101, d1747, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1747, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38671 p hg
    simpa only [d8101, d1747, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39030 (p : Pattern) (guard : d8102 p = 1) : d1748 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1748, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39027 p hg
    simpa only [d8102, d1748, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1748, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39029 p hg
    simpa only [d8102, d1748, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39031 (p : Pattern) (guard : d8095 p = 1) : d19 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d19, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34975 p hg
    simpa only [d8095, d19, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d19, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d19, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39032 (p : Pattern) (guard : d8101 p = 1) : d1698 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1698, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39031 p hg
    simpa only [d8101, d1698, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1698, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38641 p hg
    simpa only [d8101, d1698, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39033 (p : Pattern) (guard : d8100 p = 1) : d25 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d25, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34980 p hg
    simpa only [d8100, d25, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d25, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d25, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39034 (p : Pattern) (guard : d8106 p = 1) : d1706 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1706, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39033 p hg
    simpa only [d8106, d1706, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1706, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38678 p hg
    simpa only [d8106, d1706, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39035 (p : Pattern) (guard : d8107 p = 1) : d1749 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1749, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39032 p hg
    simpa only [d8107, d1749, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1749, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39034 p hg
    simpa only [d8107, d1749, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39036 (p : Pattern) (guard : d8108 p = 1) : d1750 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1750, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39030 p hg
    simpa only [d8108, d1750, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1750, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39035 p hg
    simpa only [d8108, d1750, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39037 (p : Pattern) (guard : d8100 p = 1) : d59 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d59, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34987 p hg
    simpa only [d8100, d59, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d59, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d59, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39038 (p : Pattern) (guard : d8106 p = 1) : d1754 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1754, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39037 p hg
    simpa only [d8106, d1754, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1754, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38564 p hg
    simpa only [d8106, d1754, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39039 (p : Pattern) (guard : d8107 p = 1) : d1755 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1755, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38816 p hg
    simpa only [d8107, d1755, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1755, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39038 p hg
    simpa only [d8107, d1755, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39040 (p : Pattern) (guard : d8100 p = 1) : d41 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d41, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34993 p hg
    simpa only [d8100, d41, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d41, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d41, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39041 (p : Pattern) (guard : d8106 p = 1) : d1756 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1756, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39040 p hg
    simpa only [d8106, d1756, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1756, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38569 p hg
    simpa only [d8106, d1756, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39042 (p : Pattern) (guard : d8112 p = 1) : d1757 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1757, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39041 p hg
    simpa only [d8112, d1757, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1757, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1757, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39043 (p : Pattern) (guard : d8113 p = 1) : d1758 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1758, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39039 p hg
    simpa only [d8113, d1758, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1758, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39042 p hg
    simpa only [d8113, d1758, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39044 (p : Pattern) (guard : d8114 p = 1) : d1759 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1759, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39036 p hg
    simpa only [d8114, d1759, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1759, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39043 p hg
    simpa only [d8114, d1759, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39045 (p : Pattern) (guard : d8101 p = 1) : d1726 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1726, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35384 p hg
    simpa only [d8101, d1726, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1726, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38534 p hg
    simpa only [d8101, d1726, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39046 (p : Pattern) (guard : d8106 p = 1) : d1760 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1760, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38841 p hg
    simpa only [d8106, d1760, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1760, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d1760, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39047 (p : Pattern) (guard : d8107 p = 1) : d1761 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1761, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39045 p hg
    simpa only [d8107, d1761, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1761, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39046 p hg
    simpa only [d8107, d1761, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39048 (p : Pattern) (guard : d8113 p = 1) : d1763 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1763, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39047 p hg
    simpa only [d8113, d1763, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1763, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38689 p hg
    simpa only [d8113, d1763, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39049 (p : Pattern) (guard : d8119 p = 1) : d1766 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1766, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39048 p hg
    simpa only [d8119, d1766, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1766, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38695 p hg
    simpa only [d8119, d1766, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39050 (p : Pattern) (guard : d8120 p = 1) : d1767 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1767, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39044 p hg
    simpa only [d8120, d1767, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1767, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39049 p hg
    simpa only [d8120, d1767, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39051 (p : Pattern) (guard : d8121 p = 1) : d1768 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1768, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39021 p hg
    simpa only [d8121, d1768, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1768, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39050 p hg
    simpa only [d8121, d1768, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39052 (p : Pattern) (guard : d8127 p = 1) : d1826 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1826, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39051 p hg
    simpa only [d8127, d1826, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1826, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38871 p hg
    simpa only [d8127, d1826, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39053 (p : Pattern) (guard : d8085 p = 1) : d1771 p ≤ (0 : Int) + d332 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d1771, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34332 p hg
    simpa only [d8085, d1771, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d1771, d332, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38480 p hg
    simpa only [d8085, d1771, d332, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39054 (p : Pattern) (guard : d8090 p = 1) : d1772 p ≤ (0 : Int) + d333 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d1772, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39053 p hg
    simpa only [d8090, d1772, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d1772, d333, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38702 p hg
    simpa only [d8090, d1772, d333, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39055 (p : Pattern) (guard : d8095 p = 1) : d1773 p ≤ (0 : Int) + d343 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1773, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39054 p hg
    simpa only [d8095, d1773, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1773, d343, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34367 p hg
    simpa only [d8095, d1773, d343, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39056 (p : Pattern) (guard : d8096 p = 1) : d1774 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1774, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38782 p hg
    simpa only [d8096, d1774, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1774, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39055 p hg
    simpa only [d8096, d1774, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39057 (p : Pattern) (guard : d8102 p = 1) : d1784 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1784, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39056 p hg
    simpa only [d8102, d1784, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1784, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38861 p hg
    simpa only [d8102, d1784, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39058 (p : Pattern) (guard : d8101 p = 1) : d1790 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1790, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35384 p hg
    simpa only [d8101, d1790, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1790, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38716 p hg
    simpa only [d8101, d1790, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39059 (p : Pattern) (guard : d8107 p = 1) : d1800 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1800, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39058 p hg
    simpa only [d8107, d1800, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1800, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38866 p hg
    simpa only [d8107, d1800, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
