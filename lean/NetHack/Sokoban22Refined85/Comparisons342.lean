/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons341
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare47880 (p : Pattern) (guard : d8131 p = 1) : d1420 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1420, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47876 p hg
    simpa only [d8131, d1420, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1420, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47879 p hg
    simpa only [d8131, d1420, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47881 (p : Pattern) (guard : d8137 p = 1) : d1428 p ≤ (0 : Int) + d444 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1428, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47880 p hg
    simpa only [d8137, d1428, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1428, d444, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d1428, d444, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47882 (p : Pattern) (guard : d8138 p = 1) : d1429 p ≤ (0 : Int) + d445 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1429, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47874 p hg
    simpa only [d8138, d1429, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1429, d445, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47881 p hg
    simpa only [d8138, d1429, d445, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47883 (p : Pattern) (guard : d8139 p = 1) : d1437 p ≤ (0 : Int) + d446 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d1437, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47837 p hg
    simpa only [d8139, d1437, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d1437, d446, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47882 p hg
    simpa only [d8139, d1437, d446, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47884 (p : Pattern) (guard : d8140 p = 1) : d1438 p ≤ (0 : Int) + d447 p := by
  cases selected : p 71 with
  | false =>
    have hg : d8134 p = 1 := by simpa only [d8140, d1438, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47792 p hg
    simpa only [d8140, d1438, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8139 p = 1 := by simpa only [d8140, d1438, d447, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47883 p hg
    simpa only [d8140, d1438, d447, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47885 (p : Pattern) (guard : d8101 p = 1) : d33 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d33, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34829 p hg
    simpa only [d8101, d33, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d33, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8101, d33, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47886 (p : Pattern) (guard : d8102 p = 1) : d950 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d950, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34655 p hg
    simpa only [d8102, d950, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d950, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47885 p hg
    simpa only [d8102, d950, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47887 (p : Pattern) (guard : d8108 p = 1) : d1399 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1399, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47886 p hg
    simpa only [d8108, d1399, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1399, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34952 p hg
    simpa only [d8108, d1399, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47888 (p : Pattern) (guard : d8109 p = 1) : d1400 p ≤ (0 : Int) + d363 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1400, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34951 p hg
    simpa only [d8109, d1400, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1400, d363, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47887 p hg
    simpa only [d8109, d1400, d363, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47889 (p : Pattern) (guard : d8102 p = 1) : d33 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34955 p hg
    simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35034 p hg
    simpa only [d8102, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47890 (p : Pattern) (guard : d8108 p = 1) : d1401 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1401, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47889 p hg
    simpa only [d8108, d1401, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1401, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34958 p hg
    simpa only [d8108, d1401, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47891 (p : Pattern) (guard : d8114 p = 1) : d1402 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1402, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47890 p hg
    simpa only [d8114, d1402, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1402, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34962 p hg
    simpa only [d8114, d1402, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47892 (p : Pattern) (guard : d8115 p = 1) : d1403 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1403, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47888 p hg
    simpa only [d8115, d1403, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1403, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47891 p hg
    simpa only [d8115, d1403, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47893 (p : Pattern) (guard : d8106 p = 1) : d360 p ≤ (0 : Int) + d360 p := by
  omega
theorem compare47894 (p : Pattern) (guard : d8107 p = 1) : d1165 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1165, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34788 p hg
    simpa only [d8107, d1165, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1165, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47893 p hg
    simpa only [d8107, d1165, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47895 (p : Pattern) (guard : d8108 p = 1) : d1404 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1404, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34973 p hg
    simpa only [d8108, d1404, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1404, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47894 p hg
    simpa only [d8108, d1404, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47896 (p : Pattern) (guard : d8106 p = 1) : d795 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d795, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35018 p hg
    simpa only [d8106, d795, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d795, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34700 p hg
    simpa only [d8106, d795, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47897 (p : Pattern) (guard : d8107 p = 1) : d796 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d796, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47803 p hg
    simpa only [d8107, d796, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d796, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47896 p hg
    simpa only [d8107, d796, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47898 (p : Pattern) (guard : d8113 p = 1) : d1405 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1405, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47897 p hg
    simpa only [d8113, d1405, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1405, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34996 p hg
    simpa only [d8113, d1405, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47899 (p : Pattern) (guard : d8114 p = 1) : d1406 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1406, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47895 p hg
    simpa only [d8114, d1406, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1406, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47898 p hg
    simpa only [d8114, d1406, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47900 (p : Pattern) (guard : d8113 p = 1) : d1407 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1407, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47808 p hg
    simpa only [d8113, d1407, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1407, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47762 p hg
    simpa only [d8113, d1407, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47901 (p : Pattern) (guard : d8119 p = 1) : d1408 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1408, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47900 p hg
    simpa only [d8119, d1408, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1408, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43787 p hg
    simpa only [d8119, d1408, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47902 (p : Pattern) (guard : d8120 p = 1) : d1409 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1409, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47899 p hg
    simpa only [d8120, d1409, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1409, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47901 p hg
    simpa only [d8120, d1409, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47903 (p : Pattern) (guard : d8121 p = 1) : d1410 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1410, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47892 p hg
    simpa only [d8121, d1410, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1410, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47902 p hg
    simpa only [d8121, d1410, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47904 (p : Pattern) (guard : d8127 p = 1) : d1421 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1421, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47903 p hg
    simpa only [d8127, d1421, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1421, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47835 p hg
    simpa only [d8127, d1421, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47905 (p : Pattern) (guard : d8113 p = 1) : d1411 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1411, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41392 p hg
    simpa only [d8113, d1411, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1411, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d8113, d1411, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47906 (p : Pattern) (guard : d8114 p = 1) : d1412 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1412, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34855 p hg
    simpa only [d8114, d1412, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1412, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47905 p hg
    simpa only [d8114, d1412, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47907 (p : Pattern) (guard : d8107 p = 1) : d53 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34590 p hg
    simpa only [d8107, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34722 p hg
    simpa only [d8107, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47908 (p : Pattern) (guard : d8113 p = 1) : d1413 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1413, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47907 p hg
    simpa only [d8113, d1413, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1413, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d1413, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47909 (p : Pattern) (guard : d8119 p = 1) : d1414 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1414, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47908 p hg
    simpa only [d8119, d1414, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1414, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1414, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47910 (p : Pattern) (guard : d8120 p = 1) : d1415 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1415, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47906 p hg
    simpa only [d8120, d1415, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1415, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47909 p hg
    simpa only [d8120, d1415, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47911 (p : Pattern) (guard : d8112 p = 1) : d808 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d808, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34835 p hg
    simpa only [d8112, d808, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d808, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34911 p hg
    simpa only [d8112, d808, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47912 (p : Pattern) (guard : d8118 p = 1) : d1417 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1417, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47911 p hg
    simpa only [d8118, d1417, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1417, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d1417, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47913 (p : Pattern) (guard : d8119 p = 1) : d1418 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1418, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47847 p hg
    simpa only [d8119, d1418, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1418, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47912 p hg
    simpa only [d8119, d1418, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47914 (p : Pattern) (guard : d8125 p = 1) : d1419 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1419, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47913 p hg
    simpa only [d8125, d1419, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1419, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47780 p hg
    simpa only [d8125, d1419, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47915 (p : Pattern) (guard : d8126 p = 1) : d1420 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1420, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47910 p hg
    simpa only [d8126, d1420, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1420, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47914 p hg
    simpa only [d8126, d1420, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47916 (p : Pattern) (guard : d8132 p = 1) : d1422 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1422, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47915 p hg
    simpa only [d8132, d1422, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1422, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41413 p hg
    simpa only [d8132, d1422, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47917 (p : Pattern) (guard : d8133 p = 1) : d1423 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d1423, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47904 p hg
    simpa only [d8133, d1423, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d1423, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47916 p hg
    simpa only [d8133, d1423, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47918 (p : Pattern) (guard : d8106 p = 1) : d33 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d33, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34926 p hg
    simpa only [d8106, d33, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d33, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8106, d33, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47919 (p : Pattern) (guard : d8107 p = 1) : d950 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d950, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34830 p hg
    simpa only [d8107, d950, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d950, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47918 p hg
    simpa only [d8107, d950, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47920 (p : Pattern) (guard : d8113 p = 1) : d1399 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1399, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47919 p hg
    simpa only [d8113, d1399, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1399, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d8113, d1399, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47921 (p : Pattern) (guard : d8114 p = 1) : d1400 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1400, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35031 p hg
    simpa only [d8114, d1400, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1400, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47920 p hg
    simpa only [d8114, d1400, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47922 (p : Pattern) (guard : d8107 p = 1) : d33 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35034 p hg
    simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47838 p hg
    simpa only [d8107, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47923 (p : Pattern) (guard : d8113 p = 1) : d1401 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1401, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47922 p hg
    simpa only [d8113, d1401, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1401, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d8113, d1401, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47924 (p : Pattern) (guard : d8119 p = 1) : d1402 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1402, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47923 p hg
    simpa only [d8119, d1402, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1402, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34872 p hg
    simpa only [d8119, d1402, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47925 (p : Pattern) (guard : d8120 p = 1) : d1403 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1403, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47921 p hg
    simpa only [d8120, d1403, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1403, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47924 p hg
    simpa only [d8120, d1403, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47926 (p : Pattern) (guard : d8112 p = 1) : d1181 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1181, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34884 p hg
    simpa only [d8112, d1181, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1181, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1181, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47927 (p : Pattern) (guard : d8113 p = 1) : d1416 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1416, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35048 p hg
    simpa only [d8113, d1416, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1416, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47926 p hg
    simpa only [d8113, d1416, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47928 (p : Pattern) (guard : d8112 p = 1) : d796 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d796, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35019 p hg
    simpa only [d8112, d796, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d796, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47848 p hg
    simpa only [d8112, d796, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47929 (p : Pattern) (guard : d8118 p = 1) : d1405 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1405, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47928 p hg
    simpa only [d8118, d1405, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1405, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d1405, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47930 (p : Pattern) (guard : d8119 p = 1) : d1424 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1424, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47927 p hg
    simpa only [d8119, d1424, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1424, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47929 p hg
    simpa only [d8119, d1424, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47931 (p : Pattern) (guard : d8118 p = 1) : d1407 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1407, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47849 p hg
    simpa only [d8118, d1407, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1407, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47853 p hg
    simpa only [d8118, d1407, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47932 (p : Pattern) (guard : d8124 p = 1) : d1408 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1408, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47931 p hg
    simpa only [d8124, d1408, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1408, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41454 p hg
    simpa only [d8124, d1408, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47933 (p : Pattern) (guard : d8125 p = 1) : d1425 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1425, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47930 p hg
    simpa only [d8125, d1425, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1425, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47932 p hg
    simpa only [d8125, d1425, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47934 (p : Pattern) (guard : d8126 p = 1) : d1426 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1426, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47925 p hg
    simpa only [d8126, d1426, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1426, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47933 p hg
    simpa only [d8126, d1426, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47935 (p : Pattern) (guard : d8132 p = 1) : d1427 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1427, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47934 p hg
    simpa only [d8132, d1427, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1427, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47880 p hg
    simpa only [d8132, d1427, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47936 (p : Pattern) (guard : d8119 p = 1) : d1412 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1412, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38188 p hg
    simpa only [d8119, d1412, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1412, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47859 p hg
    simpa only [d8119, d1412, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47937 (p : Pattern) (guard : d8125 p = 1) : d1415 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1415, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47936 p hg
    simpa only [d8125, d1415, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1415, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47863 p hg
    simpa only [d8125, d1415, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47938 (p : Pattern) (guard : d8118 p = 1) : d1416 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1416, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41416 p hg
    simpa only [d8118, d1416, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1416, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47865 p hg
    simpa only [d8118, d1416, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47939 (p : Pattern) (guard : d8124 p = 1) : d1418 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1418, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47938 p hg
    simpa only [d8124, d1418, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1418, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47868 p hg
    simpa only [d8124, d1418, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47940 (p : Pattern) (guard : d8130 p = 1) : d1419 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1419, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47939 p hg
    simpa only [d8130, d1419, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1419, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47871 p hg
    simpa only [d8130, d1419, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47941 (p : Pattern) (guard : d8131 p = 1) : d1420 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1420, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47937 p hg
    simpa only [d8131, d1420, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1420, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47940 p hg
    simpa only [d8131, d1420, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47942 (p : Pattern) (guard : d8137 p = 1) : d1428 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1428, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47941 p hg
    simpa only [d8137, d1428, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1428, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36809 p hg
    simpa only [d8137, d1428, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47943 (p : Pattern) (guard : d8138 p = 1) : d1429 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1429, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47935 p hg
    simpa only [d8138, d1429, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1429, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47942 p hg
    simpa only [d8138, d1429, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47944 (p : Pattern) (guard : d8139 p = 1) : d1430 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8133 p = 1 := by simpa only [d8139, d1430, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47917 p hg
    simpa only [d8139, d1430, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8138 p = 1 := by simpa only [d8139, d1430, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47943 p hg
    simpa only [d8139, d1430, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47945 (p : Pattern) (guard : d8106 p = 1) : d118 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d118, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35239 p hg
    simpa only [d8106, d118, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d118, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35214 p hg
    simpa only [d8106, d118, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47946 (p : Pattern) (guard : d8107 p = 1) : d1043 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1043, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35149 p hg
    simpa only [d8107, d1043, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1043, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47945 p hg
    simpa only [d8107, d1043, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47947 (p : Pattern) (guard : d8113 p = 1) : d1439 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1439, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47946 p hg
    simpa only [d8113, d1439, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1439, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35157 p hg
    simpa only [d8113, d1439, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47948 (p : Pattern) (guard : d8114 p = 1) : d1440 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1440, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35142 p hg
    simpa only [d8114, d1440, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1440, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47947 p hg
    simpa only [d8114, d1440, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47949 (p : Pattern) (guard : d8107 p = 1) : d118 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35173 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35315 p hg
    simpa only [d8107, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47950 (p : Pattern) (guard : d8113 p = 1) : d1441 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1441, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47949 p hg
    simpa only [d8113, d1441, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1441, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35191 p hg
    simpa only [d8113, d1441, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47951 (p : Pattern) (guard : d8119 p = 1) : d1442 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1442, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47950 p hg
    simpa only [d8119, d1442, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1442, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35197 p hg
    simpa only [d8119, d1442, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47952 (p : Pattern) (guard : d8120 p = 1) : d1443 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1443, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47948 p hg
    simpa only [d8120, d1443, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1443, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47951 p hg
    simpa only [d8120, d1443, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47953 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d119 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1275 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1571 p hg
    simpa only [d119, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47954 (p : Pattern) (guard : d8084 p = 1) : d116 p ≤ (0 : Int) + d317 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d116, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47953 p hg
    simpa only [d8084, d116, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d116, d317, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35165 p hg
    simpa only [d8084, d116, d317, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47955 (p : Pattern) (guard : d8089 p = 1) : d116 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47954 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35168 p hg
    simpa only [d8089, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47956 (p : Pattern) (guard : d8094 p = 1) : d116 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47955 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35170 p hg
    simpa only [d8094, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47957 (p : Pattern) (guard : d8100 p = 1) : d116 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47956 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35212 p hg
    simpa only [d8100, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47958 (p : Pattern) (guard : d8106 p = 1) : d132 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d132, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47957 p hg
    simpa only [d8106, d132, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d132, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35214 p hg
    simpa only [d8106, d132, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47959 (p : Pattern) (guard : d8111 p = 1) : d370 p ≤ (0 : Int) + d370 p := by
  omega
theorem compare47960 (p : Pattern) (guard : d8112 p = 1) : d1284 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1284, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47958 p hg
    simpa only [d8112, d1284, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1284, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47959 p hg
    simpa only [d8112, d1284, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47961 (p : Pattern) (guard : d8113 p = 1) : d1444 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1444, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35216 p hg
    simpa only [d8113, d1444, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1444, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47960 p hg
    simpa only [d8113, d1444, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47962 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d8 p := by
  change (3 : Int) ≤ (0 : Int) + 8
  decide
theorem compare47963 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d190 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47962 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1571 p hg
    simpa only [d190, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47964 (p : Pattern) (guard : d8084 p = 1) : d116 p ≤ (0 : Int) + d315 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d116, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47963 p hg
    simpa only [d8084, d116, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d116, d315, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35165 p hg
    simpa only [d8084, d116, d315, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47965 (p : Pattern) (guard : d8089 p = 1) : d116 p ≤ (0 : Int) + d320 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47964 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35168 p hg
    simpa only [d8089, d320, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47966 (p : Pattern) (guard : d8094 p = 1) : d116 p ≤ (0 : Int) + d321 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47965 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35170 p hg
    simpa only [d8094, d321, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47967 (p : Pattern) (guard : d8100 p = 1) : d116 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47966 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35212 p hg
    simpa only [d8100, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47968 (p : Pattern) (guard : d8106 p = 1) : d132 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d132, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47967 p hg
    simpa only [d8106, d132, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d132, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35214 p hg
    simpa only [d8106, d132, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47969 (p : Pattern) (guard : d8111 p = 1) : d861 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d861, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35282 p hg
    simpa only [d8111, d861, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d861, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5164 p hg
    simpa only [d8111, d861, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47970 (p : Pattern) (guard : d8112 p = 1) : d862 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d862, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47968 p hg
    simpa only [d8112, d862, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d862, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47969 p hg
    simpa only [d8112, d862, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47971 (p : Pattern) (guard : d8118 p = 1) : d1051 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1051, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47970 p hg
    simpa only [d8118, d1051, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1051, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1051, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47972 (p : Pattern) (guard : d8119 p = 1) : d1445 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1445, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47961 p hg
    simpa only [d8119, d1445, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1445, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47971 p hg
    simpa only [d8119, d1445, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47973 (p : Pattern) (guard : d1 p = 1) : d3 p ≤ (0 : Int) + d23 p := by
  cases selected : p 247 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4566 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d1 p = 1 := by simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1571 p hg
    simpa only [d23, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47974 (p : Pattern) (guard : d8084 p = 1) : d116 p ≤ (0 : Int) + d356 p := by
  cases selected : p 246 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8084, d116, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47973 p hg
    simpa only [d8084, d116, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5843 p = 1 := by simpa only [d8084, d116, d356, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35165 p hg
    simpa only [d8084, d116, d356, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47975 (p : Pattern) (guard : d8089 p = 1) : d116 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47974 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35168 p hg
    simpa only [d8089, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47976 (p : Pattern) (guard : d8094 p = 1) : d116 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47975 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35170 p hg
    simpa only [d8094, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47977 (p : Pattern) (guard : d8100 p = 1) : d116 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47976 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35212 p hg
    simpa only [d8100, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47978 (p : Pattern) (guard : d8106 p = 1) : d132 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d132, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47977 p hg
    simpa only [d8106, d132, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d132, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35214 p hg
    simpa only [d8106, d132, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47979 (p : Pattern) (guard : d8111 p = 1) : d861 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35241 p hg
    simpa only [d8111, d861, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d861, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5164 p hg
    simpa only [d8111, d861, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47980 (p : Pattern) (guard : d8112 p = 1) : d862 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d862, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47978 p hg
    simpa only [d8112, d862, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d862, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47979 p hg
    simpa only [d8112, d862, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47981 (p : Pattern) (guard : d8117 p = 1) : d1290 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35242 p hg
    simpa only [d8117, d1290, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1290, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1290, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47982 (p : Pattern) (guard : d8118 p = 1) : d1446 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1446, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47980 p hg
    simpa only [d8118, d1446, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1446, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47981 p hg
    simpa only [d8118, d1446, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47983 (p : Pattern) (guard : d8124 p = 1) : d1447 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1447, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47982 p hg
    simpa only [d8124, d1447, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1447, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43999 p hg
    simpa only [d8124, d1447, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47984 (p : Pattern) (guard : d8125 p = 1) : d1448 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1448, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47972 p hg
    simpa only [d8125, d1448, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1448, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47983 p hg
    simpa only [d8125, d1448, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47985 (p : Pattern) (guard : d8126 p = 1) : d1449 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1449, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47952 p hg
    simpa only [d8126, d1449, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1449, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47984 p hg
    simpa only [d8126, d1449, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47986 (p : Pattern) (guard : d8112 p = 1) : d133 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d133, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35259 p hg
    simpa only [d8112, d133, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d133, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35360 p hg
    simpa only [d8112, d133, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47987 (p : Pattern) (guard : d8118 p = 1) : d1450 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1450, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47986 p hg
    simpa only [d8118, d1450, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1450, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35261 p hg
    simpa only [d8118, d1450, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47988 (p : Pattern) (guard : d8119 p = 1) : d1451 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1451, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35258 p hg
    simpa only [d8119, d1451, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1451, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47987 p hg
    simpa only [d8119, d1451, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47989 (p : Pattern) (guard : d8112 p = 1) : d132 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35265 p hg
    simpa only [d8112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35360 p hg
    simpa only [d8112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47990 (p : Pattern) (guard : d8118 p = 1) : d1061 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47989 p hg
    simpa only [d8118, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1061, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1061, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47991 (p : Pattern) (guard : d8124 p = 1) : d1062 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47990 p hg
    simpa only [d8124, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1062, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1062, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47992 (p : Pattern) (guard : d8125 p = 1) : d1452 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1452, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47988 p hg
    simpa only [d8125, d1452, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1452, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47991 p hg
    simpa only [d8125, d1452, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47993 (p : Pattern) (guard : d8117 p = 1) : d1289 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35360 p hg
    simpa only [d8117, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1289, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1289, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47994 (p : Pattern) (guard : d8118 p = 1) : d1453 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1453, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35284 p hg
    simpa only [d8118, d1453, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1453, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47993 p hg
    simpa only [d8118, d1453, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47995 (p : Pattern) (guard : d8117 p = 1) : d873 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35360 p hg
    simpa only [d8117, d873, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d873, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3772 p hg
    simpa only [d8117, d873, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47996 (p : Pattern) (guard : d8123 p = 1) : d1064 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47995 p hg
    simpa only [d8123, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1064, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1064, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47997 (p : Pattern) (guard : d8124 p = 1) : d1454 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1454, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47994 p hg
    simpa only [d8124, d1454, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1454, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47996 p hg
    simpa only [d8124, d1454, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47998 (p : Pattern) (guard : d8129 p = 1) : d1066 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47996 p hg
    simpa only [d8129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1066, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47999 (p : Pattern) (guard : d8130 p = 1) : d1455 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1455, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47997 p hg
    simpa only [d8130, d1455, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1455, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47998 p hg
    simpa only [d8130, d1455, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48000 (p : Pattern) (guard : d8131 p = 1) : d1456 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1456, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47992 p hg
    simpa only [d8131, d1456, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1456, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47999 p hg
    simpa only [d8131, d1456, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48001 (p : Pattern) (guard : d8132 p = 1) : d1457 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1457, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47985 p hg
    simpa only [d8132, d1457, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1457, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48000 p hg
    simpa only [d8132, d1457, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48002 (p : Pattern) (guard : d8112 p = 1) : d133 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d133, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35255 p hg
    simpa only [d8112, d133, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d133, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35360 p hg
    simpa only [d8112, d133, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48003 (p : Pattern) (guard : d8118 p = 1) : d1450 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1450, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48002 p hg
    simpa only [d8118, d1450, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1450, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35261 p hg
    simpa only [d8118, d1450, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48004 (p : Pattern) (guard : d8119 p = 1) : d1451 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1451, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38202 p hg
    simpa only [d8119, d1451, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1451, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48003 p hg
    simpa only [d8119, d1451, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48005 (p : Pattern) (guard : d8112 p = 1) : d132 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38210 p hg
    simpa only [d8112, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35360 p hg
    simpa only [d8112, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48006 (p : Pattern) (guard : d8118 p = 1) : d1061 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1061, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48005 p hg
    simpa only [d8118, d1061, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1061, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d1061, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48007 (p : Pattern) (guard : d8124 p = 1) : d1062 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1062, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48006 p hg
    simpa only [d8124, d1062, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1062, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1062, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48008 (p : Pattern) (guard : d8125 p = 1) : d1452 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1452, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48004 p hg
    simpa only [d8125, d1452, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1452, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48007 p hg
    simpa only [d8125, d1452, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48009 (p : Pattern) (guard : d8117 p = 1) : d1289 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1289, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35283 p hg
    simpa only [d8117, d1289, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1289, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1289, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48010 (p : Pattern) (guard : d8118 p = 1) : d1453 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1453, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41426 p hg
    simpa only [d8118, d1453, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1453, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48009 p hg
    simpa only [d8118, d1453, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48011 (p : Pattern) (guard : d8124 p = 1) : d1454 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1454, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48010 p hg
    simpa only [d8124, d1454, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1454, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47996 p hg
    simpa only [d8124, d1454, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48012 (p : Pattern) (guard : d8130 p = 1) : d1455 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1455, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48011 p hg
    simpa only [d8130, d1455, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1455, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47998 p hg
    simpa only [d8130, d1455, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48013 (p : Pattern) (guard : d8131 p = 1) : d1456 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1456, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48008 p hg
    simpa only [d8131, d1456, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1456, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48012 p hg
    simpa only [d8131, d1456, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48014 (p : Pattern) (guard : d8137 p = 1) : d1458 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1458, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48013 p hg
    simpa only [d8137, d1458, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1458, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38220 p hg
    simpa only [d8137, d1458, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48015 (p : Pattern) (guard : d8138 p = 1) : d1459 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1459, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48001 p hg
    simpa only [d8138, d1459, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1459, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48014 p hg
    simpa only [d8138, d1459, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48016 (p : Pattern) (guard : d8111 p = 1) : d118 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35316 p hg
    simpa only [d8111, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d118, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5171 p hg
    simpa only [d8111, d118, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48017 (p : Pattern) (guard : d8112 p = 1) : d1043 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1043, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35253 p hg
    simpa only [d8112, d1043, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1043, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48016 p hg
    simpa only [d8112, d1043, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48018 (p : Pattern) (guard : d8118 p = 1) : d1439 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1439, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48017 p hg
    simpa only [d8118, d1439, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1439, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35261 p hg
    simpa only [d8118, d1439, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare48019 (p : Pattern) (guard : d8119 p = 1) : d1440 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1440, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35311 p hg
    simpa only [d8119, d1440, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1440, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare48018 p hg
    simpa only [d8119, d1440, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
