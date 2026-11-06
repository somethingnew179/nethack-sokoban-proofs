/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons311
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare43680 (p : Pattern) (guard : d8114 p = 1) : d1512 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1512, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43679 p hg
    simpa only [d8114, d1512, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1512, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34650 p hg
    simpa only [d8114, d1512, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43681 (p : Pattern) (guard : d8120 p = 1) : d1524 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1524, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43680 p hg
    simpa only [d8120, d1524, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1524, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43666 p hg
    simpa only [d8120, d1524, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43682 (p : Pattern) (guard : d8101 p = 1) : d46 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d46, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34812 p hg
    simpa only [d8101, d46, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d46, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d46, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43683 (p : Pattern) (guard : d8107 p = 1) : d1518 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1518, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43682 p hg
    simpa only [d8107, d1518, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1518, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34680 p hg
    simpa only [d8107, d1518, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43684 (p : Pattern) (guard : d8113 p = 1) : d1519 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1519, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43683 p hg
    simpa only [d8113, d1519, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1519, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34684 p hg
    simpa only [d8113, d1519, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43685 (p : Pattern) (guard : d8119 p = 1) : d1520 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1520, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43684 p hg
    simpa only [d8119, d1520, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1520, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34692 p hg
    simpa only [d8119, d1520, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43686 (p : Pattern) (guard : d8125 p = 1) : d1526 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1526, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43685 p hg
    simpa only [d8125, d1526, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1526, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43674 p hg
    simpa only [d8125, d1526, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43687 (p : Pattern) (guard : d8126 p = 1) : d1527 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1527, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43681 p hg
    simpa only [d8126, d1527, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1527, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43686 p hg
    simpa only [d8126, d1527, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43688 (p : Pattern) (guard : d8132 p = 1) : d1550 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1550, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43687 p hg
    simpa only [d8132, d1550, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1550, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d8132, d1550, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43689 (p : Pattern) (guard : d8133 p = 1) : d1551 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d1551, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43677 p hg
    simpa only [d8133, d1551, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d1551, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43688 p hg
    simpa only [d8133, d1551, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43690 (p : Pattern) (guard : d8134 p = 1) : d1552 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d1552, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43635 p hg
    simpa only [d8134, d1552, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d1552, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43689 p hg
    simpa only [d8134, d1552, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43691 (p : Pattern) (guard : d8091 p = 1) : d353 p ≤ (0 : Int) + d353 p := by
  omega
theorem compare43692 (p : Pattern) (guard : d8092 p = 1) : d1553 p ≤ (0 : Int) + d433 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d1553, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34747 p hg
    simpa only [d8092, d1553, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d1553, d433, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43691 p hg
    simpa only [d8092, d1553, d433, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43693 (p : Pattern) (guard : d8095 p = 1) : d343 p ≤ (0 : Int) + d343 p := by
  omega
theorem compare43694 (p : Pattern) (guard : d8096 p = 1) : d1507 p ≤ (0 : Int) + d344 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1507, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34751 p hg
    simpa only [d8096, d1507, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1507, d344, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43693 p hg
    simpa only [d8096, d1507, d344, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43695 (p : Pattern) (guard : d8097 p = 1) : d1554 p ≤ (0 : Int) + d434 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1554, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43692 p hg
    simpa only [d8097, d1554, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1554, d434, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43694 p hg
    simpa only [d8097, d1554, d434, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43696 (p : Pattern) (guard : d8101 p = 1) : d43 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d43, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34757 p hg
    simpa only [d8101, d43, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d43, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d43, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43697 (p : Pattern) (guard : d8102 p = 1) : d47 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d47, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43645 p hg
    simpa only [d8102, d47, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d47, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43696 p hg
    simpa only [d8102, d47, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43698 (p : Pattern) (guard : d8103 p = 1) : d1555 p ≤ (0 : Int) + d435 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1555, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43695 p hg
    simpa only [d8103, d1555, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1555, d435, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43697 p hg
    simpa only [d8103, d1555, d435, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43699 (p : Pattern) (guard : d8102 p = 1) : d47 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d47, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43613 p hg
    simpa only [d8102, d47, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d47, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43648 p hg
    simpa only [d8102, d47, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43700 (p : Pattern) (guard : d8101 p = 1) : d48 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d48, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34766 p hg
    simpa only [d8101, d48, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d48, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d48, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43701 (p : Pattern) (guard : d8107 p = 1) : d49 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d49, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43700 p hg
    simpa only [d8107, d49, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d49, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d49, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43702 (p : Pattern) (guard : d8108 p = 1) : d50 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d50, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43699 p hg
    simpa only [d8108, d50, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d50, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43701 p hg
    simpa only [d8108, d50, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43703 (p : Pattern) (guard : d8109 p = 1) : d1556 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1556, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43698 p hg
    simpa only [d8109, d1556, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1556, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43702 p hg
    simpa only [d8109, d1556, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43704 (p : Pattern) (guard : d8115 p = 1) : d1557 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1557, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43703 p hg
    simpa only [d8115, d1557, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1557, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43680 p hg
    simpa only [d8115, d1557, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43705 (p : Pattern) (guard : d8095 p = 1) : d336 p ≤ (0 : Int) + d336 p := by
  omega
theorem compare43706 (p : Pattern) (guard : d8096 p = 1) : d1505 p ≤ (0 : Int) + d337 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8091 p = 1 := by simpa only [d8096, d1505, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34780 p hg
    simpa only [d8096, d1505, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8095 p = 1 := by simpa only [d8096, d1505, d337, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43705 p hg
    simpa only [d8096, d1505, d337, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43707 (p : Pattern) (guard : d8101 p = 1) : d66 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d66, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34787 p hg
    simpa only [d8101, d66, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d66, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d66, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43708 (p : Pattern) (guard : d8102 p = 1) : d1558 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1558, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43706 p hg
    simpa only [d8102, d1558, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1558, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43707 p hg
    simpa only [d8102, d1558, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43709 (p : Pattern) (guard : d8101 p = 1) : d43 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d43, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34792 p hg
    simpa only [d8101, d43, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d43, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d43, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43710 (p : Pattern) (guard : d8106 p = 1) : d48 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d48, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34797 p hg
    simpa only [d8106, d48, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d48, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d48, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43711 (p : Pattern) (guard : d8107 p = 1) : d68 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d68, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43709 p hg
    simpa only [d8107, d68, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d68, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43710 p hg
    simpa only [d8107, d68, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43712 (p : Pattern) (guard : d8108 p = 1) : d1559 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1559, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43708 p hg
    simpa only [d8108, d1559, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1559, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43711 p hg
    simpa only [d8108, d1559, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43713 (p : Pattern) (guard : d8106 p = 1) : d70 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d70, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34805 p hg
    simpa only [d8106, d70, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d70, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d70, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43714 (p : Pattern) (guard : d8107 p = 1) : d71 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d71, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43696 p hg
    simpa only [d8107, d71, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d71, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43713 p hg
    simpa only [d8107, d71, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43715 (p : Pattern) (guard : d8113 p = 1) : d74 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d74, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43714 p hg
    simpa only [d8113, d74, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d74, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34544 p hg
    simpa only [d8113, d74, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43716 (p : Pattern) (guard : d8114 p = 1) : d1560 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1560, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43712 p hg
    simpa only [d8114, d1560, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1560, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43715 p hg
    simpa only [d8114, d1560, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43717 (p : Pattern) (guard : d8120 p = 1) : d1561 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1561, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43716 p hg
    simpa only [d8120, d1561, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1561, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43685 p hg
    simpa only [d8120, d1561, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43718 (p : Pattern) (guard : d8121 p = 1) : d1562 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1562, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43704 p hg
    simpa only [d8121, d1562, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1562, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43717 p hg
    simpa only [d8121, d1562, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43719 (p : Pattern) (guard : d8102 p = 1) : d46 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43613 p hg
    simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43682 p hg
    simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43720 (p : Pattern) (guard : d8107 p = 1) : d47 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d47, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43668 p hg
    simpa only [d8107, d47, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d47, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34644 p hg
    simpa only [d8107, d47, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43721 (p : Pattern) (guard : d8108 p = 1) : d1511 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1511, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43719 p hg
    simpa only [d8108, d1511, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1511, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43720 p hg
    simpa only [d8108, d1511, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43722 (p : Pattern) (guard : d8114 p = 1) : d1512 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1512, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43721 p hg
    simpa only [d8114, d1512, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1512, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34962 p hg
    simpa only [d8114, d1512, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43723 (p : Pattern) (guard : d8120 p = 1) : d1524 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1524, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43722 p hg
    simpa only [d8120, d1524, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1524, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43666 p hg
    simpa only [d8120, d1524, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43724 (p : Pattern) (guard : d8101 p = 1) : d46 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d46, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34829 p hg
    simpa only [d8101, d46, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d46, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d46, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43725 (p : Pattern) (guard : d8107 p = 1) : d1518 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1518, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43724 p hg
    simpa only [d8107, d1518, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1518, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35000 p hg
    simpa only [d8107, d1518, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43726 (p : Pattern) (guard : d8113 p = 1) : d1519 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1519, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43725 p hg
    simpa only [d8113, d1519, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1519, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34684 p hg
    simpa only [d8113, d1519, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43727 (p : Pattern) (guard : d8119 p = 1) : d1520 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1520, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43726 p hg
    simpa only [d8119, d1520, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1520, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34692 p hg
    simpa only [d8119, d1520, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43728 (p : Pattern) (guard : d8125 p = 1) : d1526 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1526, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43727 p hg
    simpa only [d8125, d1526, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1526, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43674 p hg
    simpa only [d8125, d1526, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43729 (p : Pattern) (guard : d8126 p = 1) : d1527 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1527, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43723 p hg
    simpa only [d8126, d1527, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1527, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43728 p hg
    simpa only [d8126, d1527, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43730 (p : Pattern) (guard : d8127 p = 1) : d1563 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1563, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43718 p hg
    simpa only [d8127, d1563, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1563, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43729 p hg
    simpa only [d8127, d1563, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43731 (p : Pattern) (guard : d8102 p = 1) : d46 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43645 p hg
    simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43724 p hg
    simpa only [d8102, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43732 (p : Pattern) (guard : d8107 p = 1) : d47 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d47, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43682 p hg
    simpa only [d8107, d47, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d47, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34644 p hg
    simpa only [d8107, d47, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43733 (p : Pattern) (guard : d8108 p = 1) : d1511 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1511, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43731 p hg
    simpa only [d8108, d1511, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1511, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43732 p hg
    simpa only [d8108, d1511, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43734 (p : Pattern) (guard : d8113 p = 1) : d50 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d50, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43720 p hg
    simpa only [d8113, d50, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d50, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34649 p hg
    simpa only [d8113, d50, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43735 (p : Pattern) (guard : d8114 p = 1) : d1512 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1512, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43733 p hg
    simpa only [d8114, d1512, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1512, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43734 p hg
    simpa only [d8114, d1512, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43736 (p : Pattern) (guard : d8107 p = 1) : d176 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d176, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34528 p hg
    simpa only [d8107, d176, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d176, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43663 p hg
    simpa only [d8107, d176, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43737 (p : Pattern) (guard : d8113 p = 1) : d177 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d177, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43736 p hg
    simpa only [d8113, d177, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d177, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34544 p hg
    simpa only [d8113, d177, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43738 (p : Pattern) (guard : d8119 p = 1) : d1523 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1523, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43737 p hg
    simpa only [d8119, d1523, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1523, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1523, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43739 (p : Pattern) (guard : d8120 p = 1) : d1524 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1524, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43735 p hg
    simpa only [d8120, d1524, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1524, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43738 p hg
    simpa only [d8120, d1524, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43740 (p : Pattern) (guard : d8101 p = 1) : d46 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d46, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34846 p hg
    simpa only [d8101, d46, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d46, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d46, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43741 (p : Pattern) (guard : d8106 p = 1) : d66 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d66, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35018 p hg
    simpa only [d8106, d66, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d66, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d66, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43742 (p : Pattern) (guard : d8107 p = 1) : d1518 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1518, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43740 p hg
    simpa only [d8107, d1518, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1518, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43741 p hg
    simpa only [d8107, d1518, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43743 (p : Pattern) (guard : d8106 p = 1) : d43 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d43, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34852 p hg
    simpa only [d8106, d43, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d43, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d43, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43744 (p : Pattern) (guard : d8112 p = 1) : d68 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d68, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43743 p hg
    simpa only [d8112, d68, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d68, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34683 p hg
    simpa only [d8112, d68, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43745 (p : Pattern) (guard : d8113 p = 1) : d1519 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1519, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43742 p hg
    simpa only [d8113, d1519, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1519, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43744 p hg
    simpa only [d8113, d1519, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43746 (p : Pattern) (guard : d8119 p = 1) : d1520 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1520, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43745 p hg
    simpa only [d8119, d1520, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1520, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34692 p hg
    simpa only [d8119, d1520, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43747 (p : Pattern) (guard : d8125 p = 1) : d1526 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1526, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43746 p hg
    simpa only [d8125, d1526, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1526, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43674 p hg
    simpa only [d8125, d1526, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43748 (p : Pattern) (guard : d8126 p = 1) : d1527 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1527, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43739 p hg
    simpa only [d8126, d1527, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1527, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43747 p hg
    simpa only [d8126, d1527, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43749 (p : Pattern) (guard : d8107 p = 1) : d1534 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1534, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43700 p hg
    simpa only [d8107, d1534, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1534, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34542 p hg
    simpa only [d8107, d1534, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43750 (p : Pattern) (guard : d8113 p = 1) : d1535 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1535, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43749 p hg
    simpa only [d8113, d1535, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1535, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34544 p hg
    simpa only [d8113, d1535, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43751 (p : Pattern) (guard : d8118 p = 1) : d1536 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34544 p hg
    simpa only [d8118, d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1536, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1536, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43752 (p : Pattern) (guard : d8119 p = 1) : d1537 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1537, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43750 p hg
    simpa only [d8119, d1537, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1537, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43751 p hg
    simpa only [d8119, d1537, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43753 (p : Pattern) (guard : d8124 p = 1) : d1538 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43751 p hg
    simpa only [d8124, d1538, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1538, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1538, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43754 (p : Pattern) (guard : d8125 p = 1) : d1539 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1539, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43752 p hg
    simpa only [d8125, d1539, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1539, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43753 p hg
    simpa only [d8125, d1539, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43755 (p : Pattern) (guard : d8130 p = 1) : d1540 p ≤ (0 : Int) + d12 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43753 p hg
    simpa only [d8130, d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1540, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36647 p hg
    simpa only [d8130, d1540, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43756 (p : Pattern) (guard : d8131 p = 1) : d1541 p ≤ (0 : Int) + d441 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1541, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43754 p hg
    simpa only [d8131, d1541, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1541, d441, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43755 p hg
    simpa only [d8131, d1541, d441, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43757 (p : Pattern) (guard : d8132 p = 1) : d1564 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1564, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43748 p hg
    simpa only [d8132, d1564, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1564, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43756 p hg
    simpa only [d8132, d1564, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43758 (p : Pattern) (guard : d8133 p = 1) : d1565 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d1565, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43730 p hg
    simpa only [d8133, d1565, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d1565, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43757 p hg
    simpa only [d8133, d1565, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43759 (p : Pattern) (guard : d8102 p = 1) : d1529 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1529, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43694 p hg
    simpa only [d8102, d1529, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1529, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43740 p hg
    simpa only [d8102, d1529, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43760 (p : Pattern) (guard : d8107 p = 1) : d47 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d47, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43724 p hg
    simpa only [d8107, d47, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d47, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43743 p hg
    simpa only [d8107, d47, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43761 (p : Pattern) (guard : d8108 p = 1) : d1530 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1530, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43759 p hg
    simpa only [d8108, d1530, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1530, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43760 p hg
    simpa only [d8108, d1530, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43762 (p : Pattern) (guard : d8113 p = 1) : d50 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d50, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43732 p hg
    simpa only [d8113, d50, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d50, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34649 p hg
    simpa only [d8113, d50, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43763 (p : Pattern) (guard : d8114 p = 1) : d1531 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1531, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43761 p hg
    simpa only [d8114, d1531, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1531, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43762 p hg
    simpa only [d8114, d1531, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43764 (p : Pattern) (guard : d8107 p = 1) : d46 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43668 p hg
    simpa only [d8107, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34869 p hg
    simpa only [d8107, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43765 (p : Pattern) (guard : d8113 p = 1) : d1511 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1511, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43764 p hg
    simpa only [d8113, d1511, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1511, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34870 p hg
    simpa only [d8113, d1511, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43766 (p : Pattern) (guard : d8119 p = 1) : d1512 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1512, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43765 p hg
    simpa only [d8119, d1512, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1512, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34872 p hg
    simpa only [d8119, d1512, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43767 (p : Pattern) (guard : d8120 p = 1) : d1566 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1566, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43763 p hg
    simpa only [d8120, d1566, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1566, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43766 p hg
    simpa only [d8120, d1566, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43768 (p : Pattern) (guard : d8101 p = 1) : d46 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d46, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34877 p hg
    simpa only [d8101, d46, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d46, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34443 p hg
    simpa only [d8101, d46, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43769 (p : Pattern) (guard : d8106 p = 1) : d66 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d66, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34883 p hg
    simpa only [d8106, d66, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d66, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d66, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43770 (p : Pattern) (guard : d8107 p = 1) : d1518 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1518, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43768 p hg
    simpa only [d8107, d1518, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1518, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43769 p hg
    simpa only [d8107, d1518, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43771 (p : Pattern) (guard : d8106 p = 1) : d43 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d43, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34889 p hg
    simpa only [d8106, d43, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d43, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d43, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43772 (p : Pattern) (guard : d8112 p = 1) : d68 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d68, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43771 p hg
    simpa only [d8112, d68, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d68, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34683 p hg
    simpa only [d8112, d68, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43773 (p : Pattern) (guard : d8113 p = 1) : d1519 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1519, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43770 p hg
    simpa only [d8113, d1519, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1519, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43772 p hg
    simpa only [d8113, d1519, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43774 (p : Pattern) (guard : d8112 p = 1) : d71 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d71, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43743 p hg
    simpa only [d8112, d71, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d71, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34687 p hg
    simpa only [d8112, d71, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43775 (p : Pattern) (guard : d8118 p = 1) : d74 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d74, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43774 p hg
    simpa only [d8118, d74, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d74, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34691 p hg
    simpa only [d8118, d74, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43776 (p : Pattern) (guard : d8119 p = 1) : d1520 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1520, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43773 p hg
    simpa only [d8119, d1520, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1520, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43775 p hg
    simpa only [d8119, d1520, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43777 (p : Pattern) (guard : d8112 p = 1) : d1518 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34869 p hg
    simpa only [d8112, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1518, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34897 p hg
    simpa only [d8112, d1518, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43778 (p : Pattern) (guard : d8118 p = 1) : d1519 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43777 p hg
    simpa only [d8118, d1519, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1519, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d8118, d1519, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43779 (p : Pattern) (guard : d8124 p = 1) : d1520 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43778 p hg
    simpa only [d8124, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1520, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34904 p hg
    simpa only [d8124, d1520, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43780 (p : Pattern) (guard : d8125 p = 1) : d1520 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43776 p hg
    simpa only [d8125, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43779 p hg
    simpa only [d8125, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43781 (p : Pattern) (guard : d8126 p = 1) : d1567 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1567, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43767 p hg
    simpa only [d8126, d1567, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1567, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43780 p hg
    simpa only [d8126, d1567, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43782 (p : Pattern) (guard : d8107 p = 1) : d46 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43682 p hg
    simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34869 p hg
    simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43783 (p : Pattern) (guard : d8113 p = 1) : d1511 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1511, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43782 p hg
    simpa only [d8113, d1511, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1511, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34870 p hg
    simpa only [d8113, d1511, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43784 (p : Pattern) (guard : d8119 p = 1) : d1512 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1512, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43783 p hg
    simpa only [d8119, d1512, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1512, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34872 p hg
    simpa only [d8119, d1512, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43785 (p : Pattern) (guard : d8111 p = 1) : d173 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34917 p hg
    simpa only [d8111, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d173, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d173, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43786 (p : Pattern) (guard : d8112 p = 1) : d176 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34680 p hg
    simpa only [d8112, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d176, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43785 p hg
    simpa only [d8112, d176, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43787 (p : Pattern) (guard : d8118 p = 1) : d177 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43786 p hg
    simpa only [d8118, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d177, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34691 p hg
    simpa only [d8118, d177, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43788 (p : Pattern) (guard : d8124 p = 1) : d1523 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43787 p hg
    simpa only [d8124, d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1523, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1523, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43789 (p : Pattern) (guard : d8125 p = 1) : d1524 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1524, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43784 p hg
    simpa only [d8125, d1524, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1524, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43788 p hg
    simpa only [d8125, d1524, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43790 (p : Pattern) (guard : d8112 p = 1) : d1518 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1518, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35578 p hg
    simpa only [d8112, d1518, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1518, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34897 p hg
    simpa only [d8112, d1518, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43791 (p : Pattern) (guard : d8118 p = 1) : d1519 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1519, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43790 p hg
    simpa only [d8118, d1519, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1519, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d8118, d1519, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43792 (p : Pattern) (guard : d8124 p = 1) : d1520 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1520, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43791 p hg
    simpa only [d8124, d1520, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1520, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34904 p hg
    simpa only [d8124, d1520, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43793 (p : Pattern) (guard : d8117 p = 1) : d183 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43785 p hg
    simpa only [d8117, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d183, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d183, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43794 (p : Pattern) (guard : d8123 p = 1) : d184 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43793 p hg
    simpa only [d8123, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d184, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d184, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43795 (p : Pattern) (guard : d8129 p = 1) : d1525 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43794 p hg
    simpa only [d8129, d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1525, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1525, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43796 (p : Pattern) (guard : d8130 p = 1) : d1526 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1526, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43792 p hg
    simpa only [d8130, d1526, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1526, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43795 p hg
    simpa only [d8130, d1526, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43797 (p : Pattern) (guard : d8131 p = 1) : d1527 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1527, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43789 p hg
    simpa only [d8131, d1527, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1527, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43796 p hg
    simpa only [d8131, d1527, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43798 (p : Pattern) (guard : d8132 p = 1) : d1568 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1568, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43781 p hg
    simpa only [d8132, d1568, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1568, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43797 p hg
    simpa only [d8132, d1568, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43799 (p : Pattern) (guard : d8107 p = 1) : d46 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43724 p hg
    simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35578 p hg
    simpa only [d8107, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43800 (p : Pattern) (guard : d8113 p = 1) : d1511 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1511, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43799 p hg
    simpa only [d8113, d1511, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1511, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34870 p hg
    simpa only [d8113, d1511, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43801 (p : Pattern) (guard : d8119 p = 1) : d1512 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1512, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43800 p hg
    simpa only [d8119, d1512, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1512, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34872 p hg
    simpa only [d8119, d1512, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43802 (p : Pattern) (guard : d8125 p = 1) : d1524 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1524, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43801 p hg
    simpa only [d8125, d1524, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1524, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43788 p hg
    simpa only [d8125, d1524, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43803 (p : Pattern) (guard : d8106 p = 1) : d46 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d46, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35072 p hg
    simpa only [d8106, d46, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d46, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d46, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43804 (p : Pattern) (guard : d8112 p = 1) : d1518 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1518, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43803 p hg
    simpa only [d8112, d1518, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1518, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34897 p hg
    simpa only [d8112, d1518, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43805 (p : Pattern) (guard : d8118 p = 1) : d1519 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1519, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43804 p hg
    simpa only [d8118, d1519, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1519, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34900 p hg
    simpa only [d8118, d1519, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43806 (p : Pattern) (guard : d8124 p = 1) : d1520 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1520, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43805 p hg
    simpa only [d8124, d1520, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1520, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34904 p hg
    simpa only [d8124, d1520, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43807 (p : Pattern) (guard : d8130 p = 1) : d1526 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1526, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43806 p hg
    simpa only [d8130, d1526, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1526, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43795 p hg
    simpa only [d8130, d1526, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43808 (p : Pattern) (guard : d8131 p = 1) : d1527 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1527, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43802 p hg
    simpa only [d8131, d1527, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1527, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43807 p hg
    simpa only [d8131, d1527, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43809 (p : Pattern) (guard : d8137 p = 1) : d1550 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1550, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43808 p hg
    simpa only [d8137, d1550, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1550, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d1550, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43810 (p : Pattern) (guard : d8138 p = 1) : d1569 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1569, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43798 p hg
    simpa only [d8138, d1569, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1569, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43809 p hg
    simpa only [d8138, d1569, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43811 (p : Pattern) (guard : d8139 p = 1) : d1570 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d1570, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43758 p hg
    simpa only [d8139, d1570, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d1570, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43810 p hg
    simpa only [d8139, d1570, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43812 (p : Pattern) (guard : d8140 p = 1) : d1571 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d1571, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43690 p hg
    simpa only [d8140, d1571, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d1571, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43811 p hg
    simpa only [d8140, d1571, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43813 (p : Pattern) (guard : d8091 p = 1) : d324 p ≤ (0 : Int) + d324 p := by
  omega
theorem compare43814 (p : Pattern) (guard : d8092 p = 1) : d1504 p ≤ (0 : Int) + d325 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8087 p = 1 := by simpa only [d8092, d1504, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34946 p hg
    simpa only [d8092, d1504, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8091 p = 1 := by simpa only [d8092, d1504, d325, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43813 p hg
    simpa only [d8092, d1504, d325, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43815 (p : Pattern) (guard : d8097 p = 1) : d1506 p ≤ (0 : Int) + d338 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8092 p = 1 := by simpa only [d8097, d1506, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43814 p hg
    simpa only [d8097, d1506, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8096 p = 1 := by simpa only [d8097, d1506, d338, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43706 p hg
    simpa only [d8097, d1506, d338, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43816 (p : Pattern) (guard : d8102 p = 1) : d1508 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d1508, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43694 p hg
    simpa only [d8102, d1508, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d1508, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43709 p hg
    simpa only [d8102, d1508, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43817 (p : Pattern) (guard : d8103 p = 1) : d1509 p ≤ (0 : Int) + d347 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8097 p = 1 := by simpa only [d8103, d1509, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43815 p hg
    simpa only [d8103, d1509, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8102 p = 1 := by simpa only [d8103, d1509, d347, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43816 p hg
    simpa only [d8103, d1509, d347, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43818 (p : Pattern) (guard : d8107 p = 1) : d49 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d49, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43562 p hg
    simpa only [d8107, d49, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d49, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d49, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare43819 (p : Pattern) (guard : d8108 p = 1) : d50 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d50, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43697 p hg
    simpa only [d8108, d50, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d50, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43818 p hg
    simpa only [d8108, d50, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
