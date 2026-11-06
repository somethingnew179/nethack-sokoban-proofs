/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons340
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare47740 (p : Pattern) (guard : d8113 p = 1) : d1417 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1417, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47739 p hg
    simpa only [d8113, d1417, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1417, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d1417, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47741 (p : Pattern) (guard : d8114 p = 1) : d1418 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1418, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47738 p hg
    simpa only [d8114, d1418, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1418, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47740 p hg
    simpa only [d8114, d1418, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47742 (p : Pattern) (guard : d8120 p = 1) : d1419 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1419, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47741 p hg
    simpa only [d8120, d1419, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1419, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47726 p hg
    simpa only [d8120, d1419, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47743 (p : Pattern) (guard : d8121 p = 1) : d1420 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1420, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47736 p hg
    simpa only [d8121, d1420, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1420, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47742 p hg
    simpa only [d8121, d1420, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47744 (p : Pattern) (guard : d8127 p = 1) : d1422 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1422, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47743 p hg
    simpa only [d8127, d1422, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1422, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41389 p hg
    simpa only [d8127, d1422, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47745 (p : Pattern) (guard : d8128 p = 1) : d1423 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8122 p = 1 := by simpa only [d8128, d1423, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47729 p hg
    simpa only [d8128, d1423, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8127 p = 1 := by simpa only [d8128, d1423, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47744 p hg
    simpa only [d8128, d1423, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47746 (p : Pattern) (guard : d8101 p = 1) : d33 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d33, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34676 p hg
    simpa only [d8101, d33, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d33, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8101, d33, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47747 (p : Pattern) (guard : d8102 p = 1) : d950 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d950, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34550 p hg
    simpa only [d8102, d950, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d950, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47746 p hg
    simpa only [d8102, d950, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47748 (p : Pattern) (guard : d8108 p = 1) : d1399 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1399, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47747 p hg
    simpa only [d8108, d1399, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1399, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34560 p hg
    simpa only [d8108, d1399, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47749 (p : Pattern) (guard : d8109 p = 1) : d1400 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1400, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34631 p hg
    simpa only [d8109, d1400, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1400, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47748 p hg
    simpa only [d8109, d1400, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47750 (p : Pattern) (guard : d8101 p = 1) : d33 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34638 p hg
    simpa only [d8101, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8101, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47751 (p : Pattern) (guard : d8102 p = 1) : d33 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34635 p hg
    simpa only [d8102, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47750 p hg
    simpa only [d8102, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47752 (p : Pattern) (guard : d8108 p = 1) : d1401 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1401, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47751 p hg
    simpa only [d8108, d1401, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1401, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34645 p hg
    simpa only [d8108, d1401, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47753 (p : Pattern) (guard : d8114 p = 1) : d1402 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1402, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47752 p hg
    simpa only [d8114, d1402, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1402, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34650 p hg
    simpa only [d8114, d1402, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47754 (p : Pattern) (guard : d8115 p = 1) : d1403 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1403, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47749 p hg
    simpa only [d8115, d1403, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1403, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47753 p hg
    simpa only [d8115, d1403, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47755 (p : Pattern) (guard : d8107 p = 1) : d1181 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1181, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41377 p hg
    simpa only [d8107, d1181, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1181, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34455 p hg
    simpa only [d8107, d1181, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47756 (p : Pattern) (guard : d8108 p = 1) : d1416 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1416, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34662 p hg
    simpa only [d8108, d1416, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1416, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47755 p hg
    simpa only [d8108, d1416, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47757 (p : Pattern) (guard : d8106 p = 1) : d795 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34679 p hg
    simpa only [d8106, d795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34700 p hg
    simpa only [d8106, d795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47758 (p : Pattern) (guard : d8107 p = 1) : d796 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d796, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34590 p hg
    simpa only [d8107, d796, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d796, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47757 p hg
    simpa only [d8107, d796, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47759 (p : Pattern) (guard : d8113 p = 1) : d1405 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1405, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47758 p hg
    simpa only [d8113, d1405, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1405, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d1405, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47760 (p : Pattern) (guard : d8114 p = 1) : d1424 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1424, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47756 p hg
    simpa only [d8114, d1424, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1424, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47759 p hg
    simpa only [d8114, d1424, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47761 (p : Pattern) (guard : d8107 p = 1) : d796 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d796, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35010 p hg
    simpa only [d8107, d796, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d796, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47757 p hg
    simpa only [d8107, d796, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47762 (p : Pattern) (guard : d8112 p = 1) : d1171 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34680 p hg
    simpa only [d8112, d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47763 (p : Pattern) (guard : d8113 p = 1) : d1407 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1407, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47761 p hg
    simpa only [d8113, d1407, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1407, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47762 p hg
    simpa only [d8113, d1407, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47764 (p : Pattern) (guard : d8119 p = 1) : d1408 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1408, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47763 p hg
    simpa only [d8119, d1408, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1408, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43787 p hg
    simpa only [d8119, d1408, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47765 (p : Pattern) (guard : d8120 p = 1) : d1425 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1425, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47760 p hg
    simpa only [d8120, d1425, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1425, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47764 p hg
    simpa only [d8120, d1425, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47766 (p : Pattern) (guard : d8121 p = 1) : d1426 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1426, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47754 p hg
    simpa only [d8121, d1426, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1426, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47765 p hg
    simpa only [d8121, d1426, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47767 (p : Pattern) (guard : d8107 p = 1) : d54 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34699 p hg
    simpa only [d8107, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34722 p hg
    simpa only [d8107, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47768 (p : Pattern) (guard : d8113 p = 1) : d1411 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47767 p hg
    simpa only [d8113, d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d8113, d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47769 (p : Pattern) (guard : d8114 p = 1) : d1412 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1412, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34703 p hg
    simpa only [d8114, d1412, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1412, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47768 p hg
    simpa only [d8114, d1412, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47770 (p : Pattern) (guard : d8107 p = 1) : d53 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34708 p hg
    simpa only [d8107, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34722 p hg
    simpa only [d8107, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47771 (p : Pattern) (guard : d8113 p = 1) : d1413 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47770 p hg
    simpa only [d8113, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47772 (p : Pattern) (guard : d8119 p = 1) : d1414 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47771 p hg
    simpa only [d8119, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47773 (p : Pattern) (guard : d8120 p = 1) : d1415 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1415, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47769 p hg
    simpa only [d8120, d1415, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1415, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47772 p hg
    simpa only [d8120, d1415, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47774 (p : Pattern) (guard : d8112 p = 1) : d1181 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34722 p hg
    simpa only [d8112, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47775 (p : Pattern) (guard : d8113 p = 1) : d1416 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1416, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34723 p hg
    simpa only [d8113, d1416, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1416, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47774 p hg
    simpa only [d8113, d1416, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47776 (p : Pattern) (guard : d8112 p = 1) : d808 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34722 p hg
    simpa only [d8112, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34911 p hg
    simpa only [d8112, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47777 (p : Pattern) (guard : d8118 p = 1) : d1417 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47776 p hg
    simpa only [d8118, d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47778 (p : Pattern) (guard : d8119 p = 1) : d1418 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1418, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47775 p hg
    simpa only [d8119, d1418, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1418, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47777 p hg
    simpa only [d8119, d1418, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47779 (p : Pattern) (guard : d8118 p = 1) : d972 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47776 p hg
    simpa only [d8118, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34734 p hg
    simpa only [d8118, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47780 (p : Pattern) (guard : d8124 p = 1) : d974 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47779 p hg
    simpa only [d8124, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47781 (p : Pattern) (guard : d8125 p = 1) : d1419 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1419, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47778 p hg
    simpa only [d8125, d1419, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1419, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47780 p hg
    simpa only [d8125, d1419, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47782 (p : Pattern) (guard : d8126 p = 1) : d1420 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1420, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47773 p hg
    simpa only [d8126, d1420, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1420, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47781 p hg
    simpa only [d8126, d1420, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47783 (p : Pattern) (guard : d8127 p = 1) : d1427 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1427, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47766 p hg
    simpa only [d8127, d1427, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1427, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47782 p hg
    simpa only [d8127, d1427, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47784 (p : Pattern) (guard : d8114 p = 1) : d1412 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1412, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38133 p hg
    simpa only [d8114, d1412, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1412, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47768 p hg
    simpa only [d8114, d1412, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47785 (p : Pattern) (guard : d8120 p = 1) : d1415 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1415, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47784 p hg
    simpa only [d8120, d1415, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1415, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47772 p hg
    simpa only [d8120, d1415, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47786 (p : Pattern) (guard : d8113 p = 1) : d1416 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1416, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41392 p hg
    simpa only [d8113, d1416, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1416, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47774 p hg
    simpa only [d8113, d1416, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47787 (p : Pattern) (guard : d8119 p = 1) : d1418 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1418, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47786 p hg
    simpa only [d8119, d1418, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1418, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47777 p hg
    simpa only [d8119, d1418, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47788 (p : Pattern) (guard : d8125 p = 1) : d1419 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1419, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47787 p hg
    simpa only [d8125, d1419, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1419, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47780 p hg
    simpa only [d8125, d1419, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47789 (p : Pattern) (guard : d8126 p = 1) : d1420 p ≤ (0 : Int) + d424 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1420, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47785 p hg
    simpa only [d8126, d1420, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1420, d424, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47788 p hg
    simpa only [d8126, d1420, d424, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47790 (p : Pattern) (guard : d8132 p = 1) : d1428 p ≤ (0 : Int) + d425 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1428, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47789 p hg
    simpa only [d8132, d1428, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1428, d425, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare36499 p hg
    simpa only [d8132, d1428, d425, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47791 (p : Pattern) (guard : d8133 p = 1) : d1429 p ≤ (0 : Int) + d426 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d1429, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47783 p hg
    simpa only [d8133, d1429, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d1429, d426, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47790 p hg
    simpa only [d8133, d1429, d426, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47792 (p : Pattern) (guard : d8134 p = 1) : d1430 p ≤ (0 : Int) + d427 p := by
  cases selected : p 115 with
  | false =>
    have hg : d8128 p = 1 := by simpa only [d8134, d1430, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47745 p hg
    simpa only [d8134, d1430, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8133 p = 1 := by simpa only [d8134, d1430, d427, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47791 p hg
    simpa only [d8134, d1430, d427, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47793 (p : Pattern) (guard : d8102 p = 1) : d950 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d950, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34622 p hg
    simpa only [d8102, d950, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d950, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35034 p hg
    simpa only [d8102, d950, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47794 (p : Pattern) (guard : d8108 p = 1) : d1399 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1399, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47793 p hg
    simpa only [d8108, d1399, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1399, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34768 p hg
    simpa only [d8108, d1399, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47795 (p : Pattern) (guard : d8109 p = 1) : d1400 p ≤ (0 : Int) + d436 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8103 p = 1 := by simpa only [d8109, d1400, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34760 p hg
    simpa only [d8109, d1400, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8108 p = 1 := by simpa only [d8109, d1400, d436, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47794 p hg
    simpa only [d8109, d1400, d436, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47796 (p : Pattern) (guard : d8102 p = 1) : d33 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8096 p = 1 := by simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34771 p hg
    simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8101 p = 1 := by simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34859 p hg
    simpa only [d8102, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47797 (p : Pattern) (guard : d8108 p = 1) : d1401 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1401, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47796 p hg
    simpa only [d8108, d1401, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1401, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34775 p hg
    simpa only [d8108, d1401, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47798 (p : Pattern) (guard : d8114 p = 1) : d1402 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1402, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47797 p hg
    simpa only [d8114, d1402, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1402, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34650 p hg
    simpa only [d8114, d1402, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47799 (p : Pattern) (guard : d8115 p = 1) : d1403 p ≤ (0 : Int) + d437 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8109 p = 1 := by simpa only [d8115, d1403, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47795 p hg
    simpa only [d8115, d1403, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8114 p = 1 := by simpa only [d8115, d1403, d437, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47798 p hg
    simpa only [d8115, d1403, d437, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47800 (p : Pattern) (guard : d8085 p = 1) : d31 p ≤ (0 : Int) + d318 p := by
  cases selected : p 225 with
  | false =>
    have hg : d1 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47693 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8084 p = 1 := by simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34408 p hg
    simpa only [d8085, d318, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47801 (p : Pattern) (guard : d8090 p = 1) : d31 p ≤ (0 : Int) + d323 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8085 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47800 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8089 p = 1 := by simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34473 p hg
    simpa only [d8090, d323, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47802 (p : Pattern) (guard : d8095 p = 1) : d31 p ≤ (0 : Int) + d324 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47801 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34526 p hg
    simpa only [d8095, d324, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47803 (p : Pattern) (guard : d8101 p = 1) : d53 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d53, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47802 p hg
    simpa only [d8101, d53, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d53, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34589 p hg
    simpa only [d8101, d53, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47804 (p : Pattern) (guard : d8106 p = 1) : d370 p ≤ (0 : Int) + d370 p := by
  omega
theorem compare47805 (p : Pattern) (guard : d8107 p = 1) : d1167 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1167, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47803 p hg
    simpa only [d8107, d1167, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1167, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47804 p hg
    simpa only [d8107, d1167, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47806 (p : Pattern) (guard : d8108 p = 1) : d1431 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8102 p = 1 := by simpa only [d8108, d1431, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34789 p hg
    simpa only [d8108, d1431, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8107 p = 1 := by simpa only [d8108, d1431, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47805 p hg
    simpa only [d8108, d1431, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47807 (p : Pattern) (guard : d8106 p = 1) : d795 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d795, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34834 p hg
    simpa only [d8106, d795, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d795, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34700 p hg
    simpa only [d8106, d795, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47808 (p : Pattern) (guard : d8107 p = 1) : d796 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d796, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34661 p hg
    simpa only [d8107, d796, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d796, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47807 p hg
    simpa only [d8107, d796, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47809 (p : Pattern) (guard : d8113 p = 1) : d1405 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1405, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47808 p hg
    simpa only [d8113, d1405, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1405, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d1405, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47810 (p : Pattern) (guard : d8114 p = 1) : d1432 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1432, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47806 p hg
    simpa only [d8114, d1432, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1432, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47809 p hg
    simpa only [d8114, d1432, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47811 (p : Pattern) (guard : d8107 p = 1) : d796 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d796, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41377 p hg
    simpa only [d8107, d796, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d796, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47757 p hg
    simpa only [d8107, d796, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47812 (p : Pattern) (guard : d8113 p = 1) : d1407 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1407, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47811 p hg
    simpa only [d8113, d1407, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1407, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47762 p hg
    simpa only [d8113, d1407, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47813 (p : Pattern) (guard : d8119 p = 1) : d1408 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1408, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47812 p hg
    simpa only [d8119, d1408, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1408, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare43787 p hg
    simpa only [d8119, d1408, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47814 (p : Pattern) (guard : d8120 p = 1) : d1433 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1433, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47810 p hg
    simpa only [d8120, d1433, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1433, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47813 p hg
    simpa only [d8120, d1433, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47815 (p : Pattern) (guard : d8121 p = 1) : d1434 p ≤ (0 : Int) + d438 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8115 p = 1 := by simpa only [d8121, d1434, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47799 p hg
    simpa only [d8121, d1434, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8120 p = 1 := by simpa only [d8121, d1434, d438, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47814 p hg
    simpa only [d8121, d1434, d438, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47816 (p : Pattern) (guard : d8107 p = 1) : d54 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d54, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34697 p hg
    simpa only [d8107, d54, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d54, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34722 p hg
    simpa only [d8107, d54, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47817 (p : Pattern) (guard : d8113 p = 1) : d1411 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1411, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47816 p hg
    simpa only [d8113, d1411, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1411, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d8113, d1411, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47818 (p : Pattern) (guard : d8114 p = 1) : d1412 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1412, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34822 p hg
    simpa only [d8114, d1412, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1412, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47817 p hg
    simpa only [d8114, d1412, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47819 (p : Pattern) (guard : d8120 p = 1) : d1415 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1415, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47818 p hg
    simpa only [d8120, d1415, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1415, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47772 p hg
    simpa only [d8120, d1415, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47820 (p : Pattern) (guard : d8113 p = 1) : d1416 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1416, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34836 p hg
    simpa only [d8113, d1416, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1416, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47774 p hg
    simpa only [d8113, d1416, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47821 (p : Pattern) (guard : d8119 p = 1) : d1418 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1418, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47820 p hg
    simpa only [d8119, d1418, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1418, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47777 p hg
    simpa only [d8119, d1418, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47822 (p : Pattern) (guard : d8125 p = 1) : d1419 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1419, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47821 p hg
    simpa only [d8125, d1419, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1419, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47780 p hg
    simpa only [d8125, d1419, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47823 (p : Pattern) (guard : d8126 p = 1) : d1420 p ≤ (0 : Int) + d439 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1420, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47819 p hg
    simpa only [d8126, d1420, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1420, d439, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47822 p hg
    simpa only [d8126, d1420, d439, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47824 (p : Pattern) (guard : d8127 p = 1) : d1435 p ≤ (0 : Int) + d440 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8121 p = 1 := by simpa only [d8127, d1435, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47815 p hg
    simpa only [d8127, d1435, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8126 p = 1 := by simpa only [d8127, d1435, d440, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47823 p hg
    simpa only [d8127, d1435, d440, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47825 (p : Pattern) (guard : d8113 p = 1) : d1411 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1411, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34723 p hg
    simpa only [d8113, d1411, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1411, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d8113, d1411, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47826 (p : Pattern) (guard : d8114 p = 1) : d1412 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1412, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35007 p hg
    simpa only [d8114, d1412, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1412, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47825 p hg
    simpa only [d8114, d1412, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47827 (p : Pattern) (guard : d8107 p = 1) : d53 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35010 p hg
    simpa only [d8107, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34722 p hg
    simpa only [d8107, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47828 (p : Pattern) (guard : d8113 p = 1) : d1413 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1413, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47827 p hg
    simpa only [d8113, d1413, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1413, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34607 p hg
    simpa only [d8113, d1413, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47829 (p : Pattern) (guard : d8119 p = 1) : d1414 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1414, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47828 p hg
    simpa only [d8119, d1414, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1414, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34613 p hg
    simpa only [d8119, d1414, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47830 (p : Pattern) (guard : d8120 p = 1) : d1415 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1415, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47826 p hg
    simpa only [d8120, d1415, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1415, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47829 p hg
    simpa only [d8120, d1415, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47831 (p : Pattern) (guard : d8112 p = 1) : d1181 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1181, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34835 p hg
    simpa only [d8112, d1181, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1181, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1181, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47832 (p : Pattern) (guard : d8113 p = 1) : d1416 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1416, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35020 p hg
    simpa only [d8113, d1416, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1416, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47831 p hg
    simpa only [d8113, d1416, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47833 (p : Pattern) (guard : d8119 p = 1) : d1418 p ≤ (0 : Int) + d398 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1418, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47832 p hg
    simpa only [d8119, d1418, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1418, d398, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47777 p hg
    simpa only [d8119, d1418, d398, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47834 (p : Pattern) (guard : d8125 p = 1) : d1419 p ≤ (0 : Int) + d399 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1419, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47833 p hg
    simpa only [d8125, d1419, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1419, d399, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47780 p hg
    simpa only [d8125, d1419, d399, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47835 (p : Pattern) (guard : d8126 p = 1) : d1420 p ≤ (0 : Int) + d400 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1420, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47830 p hg
    simpa only [d8126, d1420, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1420, d400, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47834 p hg
    simpa only [d8126, d1420, d400, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47836 (p : Pattern) (guard : d8132 p = 1) : d1422 p ≤ (0 : Int) + d442 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1422, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47835 p hg
    simpa only [d8132, d1422, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1422, d442, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41401 p hg
    simpa only [d8132, d1422, d442, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47837 (p : Pattern) (guard : d8133 p = 1) : d1436 p ≤ (0 : Int) + d443 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8127 p = 1 := by simpa only [d8133, d1436, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47824 p hg
    simpa only [d8133, d1436, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8132 p = 1 := by simpa only [d8133, d1436, d443, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47836 p hg
    simpa only [d8133, d1436, d443, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47838 (p : Pattern) (guard : d8106 p = 1) : d33 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34861 p hg
    simpa only [d8106, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d33, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34721 p hg
    simpa only [d8106, d33, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47839 (p : Pattern) (guard : d8107 p = 1) : d950 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d950, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34819 p hg
    simpa only [d8107, d950, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d950, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47838 p hg
    simpa only [d8107, d950, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47840 (p : Pattern) (guard : d8113 p = 1) : d1399 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1399, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47839 p hg
    simpa only [d8113, d1399, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1399, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34704 p hg
    simpa only [d8113, d1399, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47841 (p : Pattern) (guard : d8114 p = 1) : d1400 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8108 p = 1 := by simpa only [d8114, d1400, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34855 p hg
    simpa only [d8114, d1400, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8113 p = 1 := by simpa only [d8114, d1400, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47840 p hg
    simpa only [d8114, d1400, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47842 (p : Pattern) (guard : d8107 p = 1) : d33 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34859 p hg
    simpa only [d8107, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47838 p hg
    simpa only [d8107, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47843 (p : Pattern) (guard : d8113 p = 1) : d1401 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1401, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47842 p hg
    simpa only [d8113, d1401, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1401, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34867 p hg
    simpa only [d8113, d1401, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47844 (p : Pattern) (guard : d8119 p = 1) : d1402 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1402, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47843 p hg
    simpa only [d8119, d1402, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1402, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34872 p hg
    simpa only [d8119, d1402, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47845 (p : Pattern) (guard : d8120 p = 1) : d1403 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1403, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47841 p hg
    simpa only [d8120, d1403, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1403, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47844 p hg
    simpa only [d8120, d1403, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47846 (p : Pattern) (guard : d8112 p = 1) : d1181 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1181, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35019 p hg
    simpa only [d8112, d1181, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1181, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34543 p hg
    simpa only [d8112, d1181, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47847 (p : Pattern) (guard : d8113 p = 1) : d1416 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1416, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34885 p hg
    simpa only [d8113, d1416, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1416, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47846 p hg
    simpa only [d8113, d1416, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47848 (p : Pattern) (guard : d8111 p = 1) : d795 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34896 p hg
    simpa only [d8111, d795, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d795, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare5050 p hg
    simpa only [d8111, d795, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47849 (p : Pattern) (guard : d8112 p = 1) : d796 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d796, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34835 p hg
    simpa only [d8112, d796, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d796, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47848 p hg
    simpa only [d8112, d796, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47850 (p : Pattern) (guard : d8118 p = 1) : d1405 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1405, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47849 p hg
    simpa only [d8118, d1405, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1405, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d1405, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47851 (p : Pattern) (guard : d8119 p = 1) : d1424 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1424, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47847 p hg
    simpa only [d8119, d1424, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1424, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47850 p hg
    simpa only [d8119, d1424, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47852 (p : Pattern) (guard : d8112 p = 1) : d796 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34722 p hg
    simpa only [d8112, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d796, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47848 p hg
    simpa only [d8112, d796, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47853 (p : Pattern) (guard : d8117 p = 1) : d1171 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34897 p hg
    simpa only [d8117, d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1171, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1171, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47854 (p : Pattern) (guard : d8118 p = 1) : d1407 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47852 p hg
    simpa only [d8118, d1407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47853 p hg
    simpa only [d8118, d1407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47855 (p : Pattern) (guard : d8124 p = 1) : d1408 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47854 p hg
    simpa only [d8124, d1408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare41454 p hg
    simpa only [d8124, d1408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47856 (p : Pattern) (guard : d8125 p = 1) : d1425 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1425, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47851 p hg
    simpa only [d8125, d1425, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1425, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47855 p hg
    simpa only [d8125, d1425, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47857 (p : Pattern) (guard : d8126 p = 1) : d1426 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1426, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47845 p hg
    simpa only [d8126, d1426, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1426, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47856 p hg
    simpa only [d8126, d1426, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47858 (p : Pattern) (guard : d8112 p = 1) : d54 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34909 p hg
    simpa only [d8112, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d54, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34928 p hg
    simpa only [d8112, d54, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47859 (p : Pattern) (guard : d8118 p = 1) : d1411 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47858 p hg
    simpa only [d8118, d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34914 p hg
    simpa only [d8118, d1411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47860 (p : Pattern) (guard : d8119 p = 1) : d1412 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1412, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34913 p hg
    simpa only [d8119, d1412, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1412, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47859 p hg
    simpa only [d8119, d1412, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47861 (p : Pattern) (guard : d8112 p = 1) : d53 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34722 p hg
    simpa only [d8112, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34928 p hg
    simpa only [d8112, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47862 (p : Pattern) (guard : d8118 p = 1) : d1413 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47861 p hg
    simpa only [d8118, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34730 p hg
    simpa only [d8118, d1413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47863 (p : Pattern) (guard : d8124 p = 1) : d1414 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47862 p hg
    simpa only [d8124, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47864 (p : Pattern) (guard : d8125 p = 1) : d1415 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1415, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47860 p hg
    simpa only [d8125, d1415, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1415, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47863 p hg
    simpa only [d8125, d1415, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47865 (p : Pattern) (guard : d8117 p = 1) : d1181 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34928 p hg
    simpa only [d8117, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1181, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1181, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47866 (p : Pattern) (guard : d8118 p = 1) : d1416 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1416, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34929 p hg
    simpa only [d8118, d1416, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1416, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47865 p hg
    simpa only [d8118, d1416, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47867 (p : Pattern) (guard : d8117 p = 1) : d808 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34928 p hg
    simpa only [d8117, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d808, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare3640 p hg
    simpa only [d8117, d808, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47868 (p : Pattern) (guard : d8123 p = 1) : d1417 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47867 p hg
    simpa only [d8123, d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare4232 p hg
    simpa only [d8123, d1417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47869 (p : Pattern) (guard : d8124 p = 1) : d1418 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1418, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47866 p hg
    simpa only [d8124, d1418, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1418, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47868 p hg
    simpa only [d8124, d1418, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47870 (p : Pattern) (guard : d8123 p = 1) : d972 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47867 p hg
    simpa only [d8123, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d972, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d972, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47871 (p : Pattern) (guard : d8129 p = 1) : d974 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47870 p hg
    simpa only [d8129, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d974, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d974, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47872 (p : Pattern) (guard : d8130 p = 1) : d1419 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1419, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47869 p hg
    simpa only [d8130, d1419, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1419, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47871 p hg
    simpa only [d8130, d1419, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47873 (p : Pattern) (guard : d8131 p = 1) : d1420 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1420, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47864 p hg
    simpa only [d8131, d1420, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1420, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47872 p hg
    simpa only [d8131, d1420, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47874 (p : Pattern) (guard : d8132 p = 1) : d1427 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1427, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47857 p hg
    simpa only [d8132, d1427, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1427, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47873 p hg
    simpa only [d8132, d1427, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47875 (p : Pattern) (guard : d8119 p = 1) : d1412 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1412, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35066 p hg
    simpa only [d8119, d1412, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1412, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47859 p hg
    simpa only [d8119, d1412, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47876 (p : Pattern) (guard : d8125 p = 1) : d1415 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1415, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47875 p hg
    simpa only [d8125, d1415, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1415, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47863 p hg
    simpa only [d8125, d1415, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47877 (p : Pattern) (guard : d8118 p = 1) : d1416 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1416, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35074 p hg
    simpa only [d8118, d1416, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1416, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47865 p hg
    simpa only [d8118, d1416, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47878 (p : Pattern) (guard : d8124 p = 1) : d1418 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1418, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47877 p hg
    simpa only [d8124, d1418, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1418, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47868 p hg
    simpa only [d8124, d1418, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare47879 (p : Pattern) (guard : d8130 p = 1) : d1419 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1419, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47878 p hg
    simpa only [d8130, d1419, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1419, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare47871 p hg
    simpa only [d8130, d1419, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
