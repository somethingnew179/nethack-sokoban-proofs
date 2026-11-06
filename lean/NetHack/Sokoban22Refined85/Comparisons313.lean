/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons312
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare43820 (p : Pattern) (guard : d8109 p = 1) : d1510 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1510, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43817 p hg
    simpa only [d8109, d1510, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1510, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43819 p hg
    simpa only [d8109, d1510, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43821 (p : Pattern) (guard : d8115 p = 1) : d1513 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1513, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43820 p hg
    simpa only [d8115, d1513, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1513, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43722 p hg
    simpa only [d8115, d1513, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43822 (p : Pattern) (guard : d8095 p = 1) : d359 p ≤ (0 : Int) + d359 p := by
  omega
theorem compare43823 (p : Pattern) (guard : d8096 p = 1) : d1514 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1514, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34966 p hg
    simpa only [d8096, d1514, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1514, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43822 p hg
    simpa only [d8096, d1514, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43824 (p : Pattern) (guard : d8101 p = 1) : d66 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d66, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34971 p hg
    simpa only [d8101, d66, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d66, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d66, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43825 (p : Pattern) (guard : d8102 p = 1) : d1515 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1515, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43823 p hg
    simpa only [d8102, d1515, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1515, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43824 p hg
    simpa only [d8102, d1515, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43826 (p : Pattern) (guard : d8101 p = 1) : d43 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d43, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34976 p hg
    simpa only [d8101, d43, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d43, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d43, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43827 (p : Pattern) (guard : d8106 p = 1) : d48 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d48, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34981 p hg
    simpa only [d8106, d48, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d48, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d48, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43828 (p : Pattern) (guard : d8107 p = 1) : d68 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d68, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43826 p hg
    simpa only [d8107, d68, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d68, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43827 p hg
    simpa only [d8107, d68, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43829 (p : Pattern) (guard : d8108 p = 1) : d1516 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1516, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43825 p hg
    simpa only [d8108, d1516, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1516, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43828 p hg
    simpa only [d8108, d1516, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43830 (p : Pattern) (guard : d8106 p = 1) : d70 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d70, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34988 p hg
    simpa only [d8106, d70, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d70, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d70, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43831 (p : Pattern) (guard : d8107 p = 1) : d71 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d71, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43709 p hg
    simpa only [d8107, d71, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d71, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43830 p hg
    simpa only [d8107, d71, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43832 (p : Pattern) (guard : d8106 p = 1) : d72 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d72, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34994 p hg
    simpa only [d8106, d72, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d72, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d72, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43833 (p : Pattern) (guard : d8112 p = 1) : d73 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d73, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43832 p hg
    simpa only [d8112, d73, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d73, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d73, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43834 (p : Pattern) (guard : d8113 p = 1) : d74 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d74, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43831 p hg
    simpa only [d8113, d74, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d74, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43833 p hg
    simpa only [d8113, d74, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43835 (p : Pattern) (guard : d8114 p = 1) : d1517 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1517, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43829 p hg
    simpa only [d8114, d1517, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1517, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43834 p hg
    simpa only [d8114, d1517, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43836 (p : Pattern) (guard : d8120 p = 1) : d1521 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1521, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43835 p hg
    simpa only [d8120, d1521, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1521, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43727 p hg
    simpa only [d8120, d1521, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43837 (p : Pattern) (guard : d8121 p = 1) : d1522 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1522, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43821 p hg
    simpa only [d8121, d1522, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1522, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43836 p hg
    simpa only [d8121, d1522, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43838 (p : Pattern) (guard : d8127 p = 1) : d1528 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1528, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43837 p hg
    simpa only [d8127, d1528, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1528, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43748 p hg
    simpa only [d8127, d1528, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43839 (p : Pattern) (guard : d8107 p = 1) : d176 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d176, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43591 p hg
    simpa only [d8107, d176, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d176, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43663 p hg
    simpa only [d8107, d176, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43840 (p : Pattern) (guard : d8113 p = 1) : d177 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d177, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43839 p hg
    simpa only [d8113, d177, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d177, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34544 p hg
    simpa only [d8113, d177, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43841 (p : Pattern) (guard : d8119 p = 1) : d1523 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1523, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43840 p hg
    simpa only [d8119, d1523, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1523, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1523, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43842 (p : Pattern) (guard : d8120 p = 1) : d1532 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1532, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43763 p hg
    simpa only [d8120, d1532, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1532, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43841 p hg
    simpa only [d8120, d1532, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43843 (p : Pattern) (guard : d8125 p = 1) : d1526 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1526, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43776 p hg
    simpa only [d8125, d1526, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1526, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43674 p hg
    simpa only [d8125, d1526, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43844 (p : Pattern) (guard : d8126 p = 1) : d1533 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1533, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43842 p hg
    simpa only [d8126, d1533, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1533, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43843 p hg
    simpa only [d8126, d1533, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43845 (p : Pattern) (guard : d8107 p = 1) : d1534 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1534, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43562 p hg
    simpa only [d8107, d1534, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1534, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34542 p hg
    simpa only [d8107, d1534, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43846 (p : Pattern) (guard : d8113 p = 1) : d1535 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1535, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43845 p hg
    simpa only [d8113, d1535, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1535, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34544 p hg
    simpa only [d8113, d1535, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43847 (p : Pattern) (guard : d8119 p = 1) : d1537 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1537, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43846 p hg
    simpa only [d8119, d1537, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1537, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43751 p hg
    simpa only [d8119, d1537, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43848 (p : Pattern) (guard : d8125 p = 1) : d1539 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1539, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43847 p hg
    simpa only [d8125, d1539, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1539, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43753 p hg
    simpa only [d8125, d1539, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43849 (p : Pattern) (guard : d8118 p = 1) : d1536 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1536, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43833 p hg
    simpa only [d8118, d1536, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1536, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1536, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43850 (p : Pattern) (guard : d8124 p = 1) : d1538 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1538, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43849 p hg
    simpa only [d8124, d1538, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1538, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1538, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43851 (p : Pattern) (guard : d8130 p = 1) : d1540 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1540, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43850 p hg
    simpa only [d8130, d1540, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1540, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d1540, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43852 (p : Pattern) (guard : d8131 p = 1) : d1541 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1541, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43848 p hg
    simpa only [d8131, d1541, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1541, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43851 p hg
    simpa only [d8131, d1541, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43853 (p : Pattern) (guard : d8132 p = 1) : d1542 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1542, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43844 p hg
    simpa only [d8132, d1542, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1542, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43852 p hg
    simpa only [d8132, d1542, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43854 (p : Pattern) (guard : d8133 p = 1) : d1543 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d1543, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43838 p hg
    simpa only [d8133, d1543, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d1543, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43853 p hg
    simpa only [d8133, d1543, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43855 (p : Pattern) (guard : d8102 p = 1) : d1544 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1544, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43706 p hg
    simpa only [d8102, d1544, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1544, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43768 p hg
    simpa only [d8102, d1544, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43856 (p : Pattern) (guard : d8107 p = 1) : d47 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d47, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43740 p hg
    simpa only [d8107, d47, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d47, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43771 p hg
    simpa only [d8107, d47, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43857 (p : Pattern) (guard : d8108 p = 1) : d1545 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1545, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43855 p hg
    simpa only [d8108, d1545, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1545, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43856 p hg
    simpa only [d8108, d1545, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43858 (p : Pattern) (guard : d8113 p = 1) : d50 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d50, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43760 p hg
    simpa only [d8113, d50, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d50, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34649 p hg
    simpa only [d8113, d50, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43859 (p : Pattern) (guard : d8114 p = 1) : d1546 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1546, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43857 p hg
    simpa only [d8114, d1546, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1546, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43858 p hg
    simpa only [d8114, d1546, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43860 (p : Pattern) (guard : d8120 p = 1) : d1547 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1547, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43859 p hg
    simpa only [d8120, d1547, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1547, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43784 p hg
    simpa only [d8120, d1547, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43861 (p : Pattern) (guard : d8101 p = 1) : d46 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d46, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35041 p hg
    simpa only [d8101, d46, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d46, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d46, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43862 (p : Pattern) (guard : d8106 p = 1) : d66 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d66, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35046 p hg
    simpa only [d8106, d66, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d66, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d66, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43863 (p : Pattern) (guard : d8107 p = 1) : d1518 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1518, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43861 p hg
    simpa only [d8107, d1518, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1518, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43862 p hg
    simpa only [d8107, d1518, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43864 (p : Pattern) (guard : d8106 p = 1) : d43 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d43, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35052 p hg
    simpa only [d8106, d43, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d43, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d43, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43865 (p : Pattern) (guard : d8112 p = 1) : d68 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d68, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43864 p hg
    simpa only [d8112, d68, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d68, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34683 p hg
    simpa only [d8112, d68, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43866 (p : Pattern) (guard : d8113 p = 1) : d1519 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1519, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43863 p hg
    simpa only [d8113, d1519, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1519, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43865 p hg
    simpa only [d8113, d1519, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43867 (p : Pattern) (guard : d8112 p = 1) : d71 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d71, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43771 p hg
    simpa only [d8112, d71, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d71, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34687 p hg
    simpa only [d8112, d71, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43868 (p : Pattern) (guard : d8118 p = 1) : d74 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d74, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43867 p hg
    simpa only [d8118, d74, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d74, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34691 p hg
    simpa only [d8118, d74, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43869 (p : Pattern) (guard : d8119 p = 1) : d1520 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1520, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43866 p hg
    simpa only [d8119, d1520, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1520, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43868 p hg
    simpa only [d8119, d1520, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43870 (p : Pattern) (guard : d8125 p = 1) : d1520 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43869 p hg
    simpa only [d8125, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43792 p hg
    simpa only [d8125, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43871 (p : Pattern) (guard : d8126 p = 1) : d1548 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1548, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43860 p hg
    simpa only [d8126, d1548, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1548, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43870 p hg
    simpa only [d8126, d1548, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43872 (p : Pattern) (guard : d8132 p = 1) : d1549 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1549, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43871 p hg
    simpa only [d8132, d1549, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1549, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43808 p hg
    simpa only [d8132, d1549, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43873 (p : Pattern) (guard : d8107 p = 1) : d46 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43740 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43803 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43874 (p : Pattern) (guard : d8113 p = 1) : d1511 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1511, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43873 p hg
    simpa only [d8113, d1511, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1511, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35579 p hg
    simpa only [d8113, d1511, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43875 (p : Pattern) (guard : d8119 p = 1) : d1512 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1512, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43874 p hg
    simpa only [d8119, d1512, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1512, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34872 p hg
    simpa only [d8119, d1512, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43876 (p : Pattern) (guard : d8125 p = 1) : d1524 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1524, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43875 p hg
    simpa only [d8125, d1524, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1524, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43788 p hg
    simpa only [d8125, d1524, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43877 (p : Pattern) (guard : d8106 p = 1) : d46 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d46, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35447 p hg
    simpa only [d8106, d46, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d46, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d46, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43878 (p : Pattern) (guard : d8112 p = 1) : d1518 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1518, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43877 p hg
    simpa only [d8112, d1518, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1518, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34897 p hg
    simpa only [d8112, d1518, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43879 (p : Pattern) (guard : d8118 p = 1) : d1519 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1519, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43878 p hg
    simpa only [d8118, d1519, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1519, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d8118, d1519, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43880 (p : Pattern) (guard : d8124 p = 1) : d1520 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1520, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43879 p hg
    simpa only [d8124, d1520, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1520, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34904 p hg
    simpa only [d8124, d1520, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43881 (p : Pattern) (guard : d8130 p = 1) : d1526 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1526, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43880 p hg
    simpa only [d8130, d1526, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1526, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43795 p hg
    simpa only [d8130, d1526, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43882 (p : Pattern) (guard : d8131 p = 1) : d1527 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1527, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43876 p hg
    simpa only [d8131, d1527, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1527, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43881 p hg
    simpa only [d8131, d1527, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43883 (p : Pattern) (guard : d8137 p = 1) : d1550 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1550, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43882 p hg
    simpa only [d8137, d1550, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1550, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d1550, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43884 (p : Pattern) (guard : d8138 p = 1) : d1551 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1551, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43872 p hg
    simpa only [d8138, d1551, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1551, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43883 p hg
    simpa only [d8138, d1551, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43885 (p : Pattern) (guard : d8139 p = 1) : d1552 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d1552, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43854 p hg
    simpa only [d8139, d1552, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d1552, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43884 p hg
    simpa only [d8139, d1552, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43886 (p : Pattern) (guard : d8095 p = 1) : d353 p ≤ (0 : Int) + d353 p := by
  omega
theorem compare43887 (p : Pattern) (guard : d8096 p = 1) : d1572 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1572, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35102 p hg
    simpa only [d8096, d1572, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1572, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43886 p hg
    simpa only [d8096, d1572, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43888 (p : Pattern) (guard : d8100 p = 1) : d343 p ≤ (0 : Int) + d343 p := by
  omega
theorem compare43889 (p : Pattern) (guard : d8101 p = 1) : d1573 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1573, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35116 p hg
    simpa only [d8101, d1573, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1573, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43888 p hg
    simpa only [d8101, d1573, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43890 (p : Pattern) (guard : d8102 p = 1) : d1574 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1574, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43887 p hg
    simpa only [d8102, d1574, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1574, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43889 p hg
    simpa only [d8102, d1574, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43891 (p : Pattern) (guard : d8101 p = 1) : d124 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d124, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35125 p hg
    simpa only [d8101, d124, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d124, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d124, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43892 (p : Pattern) (guard : d8106 p = 1) : d125 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d125, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35138 p hg
    simpa only [d8106, d125, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d125, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d125, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43893 (p : Pattern) (guard : d8107 p = 1) : d126 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d126, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43891 p hg
    simpa only [d8107, d126, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d126, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43892 p hg
    simpa only [d8107, d126, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43894 (p : Pattern) (guard : d8108 p = 1) : d1575 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1575, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43890 p hg
    simpa only [d8108, d1575, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1575, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43893 p hg
    simpa only [d8108, d1575, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43895 (p : Pattern) (guard : d8101 p = 1) : d124 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d124, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35148 p hg
    simpa only [d8101, d124, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d124, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d124, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43896 (p : Pattern) (guard : d8106 p = 1) : d125 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d125, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35154 p hg
    simpa only [d8106, d125, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d125, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d125, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43897 (p : Pattern) (guard : d8107 p = 1) : d126 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d126, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43895 p hg
    simpa only [d8107, d126, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d126, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43896 p hg
    simpa only [d8107, d126, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43898 (p : Pattern) (guard : d8112 p = 1) : d128 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d128, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43830 p hg
    simpa only [d8112, d128, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d128, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d128, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43899 (p : Pattern) (guard : d8113 p = 1) : d129 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d129, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43897 p hg
    simpa only [d8113, d129, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d129, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43898 p hg
    simpa only [d8113, d129, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43900 (p : Pattern) (guard : d8114 p = 1) : d1576 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1576, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43894 p hg
    simpa only [d8114, d1576, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1576, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43899 p hg
    simpa only [d8114, d1576, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43901 (p : Pattern) (guard : d8101 p = 1) : d124 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d124, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35164 p hg
    simpa only [d8101, d124, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d124, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d124, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43902 (p : Pattern) (guard : d8106 p = 1) : d124 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d124, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35179 p hg
    simpa only [d8106, d124, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d124, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d124, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43903 (p : Pattern) (guard : d8107 p = 1) : d124 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43901 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43902 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43904 (p : Pattern) (guard : d8113 p = 1) : d1577 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1577, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43903 p hg
    simpa only [d8113, d1577, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1577, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35191 p hg
    simpa only [d8113, d1577, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43905 (p : Pattern) (guard : d8119 p = 1) : d1578 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1578, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43904 p hg
    simpa only [d8119, d1578, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1578, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35197 p hg
    simpa only [d8119, d1578, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43906 (p : Pattern) (guard : d8120 p = 1) : d1579 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1579, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43900 p hg
    simpa only [d8120, d1579, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1579, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43905 p hg
    simpa only [d8120, d1579, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43907 (p : Pattern) (guard : d8100 p = 1) : d336 p ≤ (0 : Int) + d336 p := by
  omega
theorem compare43908 (p : Pattern) (guard : d8101 p = 1) : d1580 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1580, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35204 p hg
    simpa only [d8101, d1580, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1580, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43907 p hg
    simpa only [d8101, d1580, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43909 (p : Pattern) (guard : d8106 p = 1) : d139 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d139, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35213 p hg
    simpa only [d8106, d139, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d139, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d139, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43910 (p : Pattern) (guard : d8107 p = 1) : d1581 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1581, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43908 p hg
    simpa only [d8107, d1581, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1581, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43909 p hg
    simpa only [d8107, d1581, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43911 (p : Pattern) (guard : d8106 p = 1) : d125 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d125, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35221 p hg
    simpa only [d8106, d125, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d125, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d125, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43912 (p : Pattern) (guard : d8111 p = 1) : d70 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d70, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35225 p hg
    simpa only [d8111, d70, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d70, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d70, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43913 (p : Pattern) (guard : d8112 p = 1) : d141 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d141, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43911 p hg
    simpa only [d8112, d141, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d141, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43912 p hg
    simpa only [d8112, d141, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43914 (p : Pattern) (guard : d8113 p = 1) : d1582 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1582, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43910 p hg
    simpa only [d8113, d1582, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1582, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43913 p hg
    simpa only [d8113, d1582, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43915 (p : Pattern) (guard : d8111 p = 1) : d72 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d72, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35231 p hg
    simpa only [d8111, d72, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d72, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d72, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43916 (p : Pattern) (guard : d8112 p = 1) : d143 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d143, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43892 p hg
    simpa only [d8112, d143, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d143, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43915 p hg
    simpa only [d8112, d143, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43917 (p : Pattern) (guard : d8118 p = 1) : d144 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d144, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43916 p hg
    simpa only [d8118, d144, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d144, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d144, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43918 (p : Pattern) (guard : d8119 p = 1) : d1583 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1583, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43914 p hg
    simpa only [d8119, d1583, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1583, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43917 p hg
    simpa only [d8119, d1583, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43919 (p : Pattern) (guard : d8106 p = 1) : d124 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d124, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35239 p hg
    simpa only [d8106, d124, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d124, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d124, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43920 (p : Pattern) (guard : d8112 p = 1) : d1584 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1584, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43919 p hg
    simpa only [d8112, d1584, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1584, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35242 p hg
    simpa only [d8112, d1584, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43921 (p : Pattern) (guard : d8118 p = 1) : d1585 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1585, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43920 p hg
    simpa only [d8118, d1585, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1585, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35244 p hg
    simpa only [d8118, d1585, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43922 (p : Pattern) (guard : d8124 p = 1) : d1586 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1586, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43921 p hg
    simpa only [d8124, d1586, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1586, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35248 p hg
    simpa only [d8124, d1586, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43923 (p : Pattern) (guard : d8125 p = 1) : d1587 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1587, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43918 p hg
    simpa only [d8125, d1587, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1587, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43922 p hg
    simpa only [d8125, d1587, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43924 (p : Pattern) (guard : d8126 p = 1) : d1588 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1588, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43906 p hg
    simpa only [d8126, d1588, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1588, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43923 p hg
    simpa only [d8126, d1588, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43925 (p : Pattern) (guard : d8107 p = 1) : d124 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43895 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43919 p hg
    simpa only [d8107, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43926 (p : Pattern) (guard : d8112 p = 1) : d126 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d126, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43902 p hg
    simpa only [d8112, d126, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d126, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35190 p hg
    simpa only [d8112, d126, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43927 (p : Pattern) (guard : d8113 p = 1) : d1577 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1577, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43925 p hg
    simpa only [d8113, d1577, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1577, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43926 p hg
    simpa only [d8113, d1577, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43928 (p : Pattern) (guard : d8118 p = 1) : d129 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d129, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35191 p hg
    simpa only [d8118, d129, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d129, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35196 p hg
    simpa only [d8118, d129, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43929 (p : Pattern) (guard : d8119 p = 1) : d1578 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1578, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43927 p hg
    simpa only [d8119, d1578, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1578, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43928 p hg
    simpa only [d8119, d1578, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43930 (p : Pattern) (guard : d8106 p = 1) : d139 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35264 p hg
    simpa only [d8106, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d139, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d139, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43931 (p : Pattern) (guard : d8111 p = 1) : d229 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35266 p hg
    simpa only [d8111, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d229, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d229, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43932 (p : Pattern) (guard : d8112 p = 1) : d1053 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43930 p hg
    simpa only [d8112, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1053, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43931 p hg
    simpa only [d8112, d1053, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43933 (p : Pattern) (guard : d8118 p = 1) : d1054 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43932 p hg
    simpa only [d8118, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1054, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1054, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43934 (p : Pattern) (guard : d8124 p = 1) : d1589 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43933 p hg
    simpa only [d8124, d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1589, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1589, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43935 (p : Pattern) (guard : d8125 p = 1) : d1590 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1590, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43929 p hg
    simpa only [d8125, d1590, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1590, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43934 p hg
    simpa only [d8125, d1590, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43936 (p : Pattern) (guard : d8106 p = 1) : d124 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d124, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35275 p hg
    simpa only [d8106, d124, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d124, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d124, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43937 (p : Pattern) (guard : d8111 p = 1) : d139 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d139, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35282 p hg
    simpa only [d8111, d139, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d139, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d139, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43938 (p : Pattern) (guard : d8112 p = 1) : d1584 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1584, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43936 p hg
    simpa only [d8112, d1584, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1584, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43937 p hg
    simpa only [d8112, d1584, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43939 (p : Pattern) (guard : d8118 p = 1) : d1585 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1585, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43938 p hg
    simpa only [d8118, d1585, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1585, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35244 p hg
    simpa only [d8118, d1585, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43940 (p : Pattern) (guard : d8124 p = 1) : d1586 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1586, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43939 p hg
    simpa only [d8124, d1586, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1586, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35248 p hg
    simpa only [d8124, d1586, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43941 (p : Pattern) (guard : d8117 p = 1) : d230 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43931 p hg
    simpa only [d8117, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d230, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d230, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43942 (p : Pattern) (guard : d8123 p = 1) : d231 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43941 p hg
    simpa only [d8123, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d231, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d231, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43943 (p : Pattern) (guard : d8129 p = 1) : d1591 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43942 p hg
    simpa only [d8129, d1591, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1591, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1591, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43944 (p : Pattern) (guard : d8130 p = 1) : d1592 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1592, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43940 p hg
    simpa only [d8130, d1592, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1592, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43943 p hg
    simpa only [d8130, d1592, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43945 (p : Pattern) (guard : d8131 p = 1) : d1593 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1593, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43935 p hg
    simpa only [d8131, d1593, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1593, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43944 p hg
    simpa only [d8131, d1593, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43946 (p : Pattern) (guard : d8132 p = 1) : d1594 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1594, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43924 p hg
    simpa only [d8132, d1594, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1594, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43945 p hg
    simpa only [d8132, d1594, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43947 (p : Pattern) (guard : d8107 p = 1) : d124 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43891 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43936 p hg
    simpa only [d8107, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43948 (p : Pattern) (guard : d8112 p = 1) : d126 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d126, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43919 p hg
    simpa only [d8112, d126, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d126, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35190 p hg
    simpa only [d8112, d126, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43949 (p : Pattern) (guard : d8113 p = 1) : d1577 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1577, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43947 p hg
    simpa only [d8113, d1577, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1577, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43948 p hg
    simpa only [d8113, d1577, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43950 (p : Pattern) (guard : d8118 p = 1) : d129 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d129, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43926 p hg
    simpa only [d8118, d129, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d129, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35196 p hg
    simpa only [d8118, d129, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43951 (p : Pattern) (guard : d8119 p = 1) : d1578 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1578, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43949 p hg
    simpa only [d8119, d1578, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1578, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43950 p hg
    simpa only [d8119, d1578, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43952 (p : Pattern) (guard : d8106 p = 1) : d139 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d139, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38209 p hg
    simpa only [d8106, d139, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d139, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d139, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43953 (p : Pattern) (guard : d8112 p = 1) : d1053 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1053, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43952 p hg
    simpa only [d8112, d1053, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1053, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43931 p hg
    simpa only [d8112, d1053, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43954 (p : Pattern) (guard : d8118 p = 1) : d1054 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1054, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43953 p hg
    simpa only [d8118, d1054, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1054, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1054, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43955 (p : Pattern) (guard : d8124 p = 1) : d1589 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1589, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43954 p hg
    simpa only [d8124, d1589, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1589, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1589, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43956 (p : Pattern) (guard : d8125 p = 1) : d1590 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1590, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43951 p hg
    simpa only [d8125, d1590, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1590, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43955 p hg
    simpa only [d8125, d1590, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43957 (p : Pattern) (guard : d8106 p = 1) : d124 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d124, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35301 p hg
    simpa only [d8106, d124, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d124, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d124, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43958 (p : Pattern) (guard : d8111 p = 1) : d139 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d139, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41424 p hg
    simpa only [d8111, d139, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d139, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d139, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43959 (p : Pattern) (guard : d8112 p = 1) : d1584 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1584, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43957 p hg
    simpa only [d8112, d1584, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1584, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43958 p hg
    simpa only [d8112, d1584, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
