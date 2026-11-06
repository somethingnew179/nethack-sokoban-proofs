/- Generated from untrusted data; every claim checked by the Lean kernel. -/
import NetHack.Sokoban22Refined85.Comparisons282
set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option linter.unusedSimpArgs false
set_option linter.unusedVariables false
namespace NetHack.Sokoban22Refined85
open NetHack.Sokoban NetHack.Sokoban.LowerBounds NetHack.Sokoban.PatternCorrection
theorem compare39620 (p : Pattern) (guard : d8112 p = 1) : d1733 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1733, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39619 p hg
    simpa only [d8112, d1733, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1733, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38906 p hg
    simpa only [d8112, d1733, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39621 (p : Pattern) (guard : d8113 p = 1) : d1734 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1734, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39618 p hg
    simpa only [d8113, d1734, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1734, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39620 p hg
    simpa only [d8113, d1734, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39622 (p : Pattern) (guard : d8106 p = 1) : d1735 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1735, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35389 p hg
    simpa only [d8106, d1735, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1735, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34532 p hg
    simpa only [d8106, d1735, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39623 (p : Pattern) (guard : d8112 p = 1) : d1736 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1736, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39622 p hg
    simpa only [d8112, d1736, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1736, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38906 p hg
    simpa only [d8112, d1736, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39624 (p : Pattern) (guard : d8118 p = 1) : d1737 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1737, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39623 p hg
    simpa only [d8118, d1737, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1737, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38911 p hg
    simpa only [d8118, d1737, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39625 (p : Pattern) (guard : d8119 p = 1) : d1738 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1738, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39621 p hg
    simpa only [d8119, d1738, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1738, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39624 p hg
    simpa only [d8119, d1738, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39626 (p : Pattern) (guard : d8120 p = 1) : d1739 p ≤ (0 : Int) + d377 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8114 p = 1 := by simpa only [d8120, d1739, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39616 p hg
    simpa only [d8120, d1739, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8119 p = 1 := by simpa only [d8120, d1739, d377, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39625 p hg
    simpa only [d8120, d1739, d377, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39627 (p : Pattern) (guard : d8094 p = 1) : d335 p ≤ (0 : Int) + d335 p := by
  omega
theorem compare39628 (p : Pattern) (guard : d8095 p = 1) : d1740 p ≤ (0 : Int) + d382 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8090 p = 1 := by simpa only [d8095, d1740, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35584 p hg
    simpa only [d8095, d1740, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8094 p = 1 := by simpa only [d8095, d1740, d382, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39627 p hg
    simpa only [d8095, d1740, d382, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39629 (p : Pattern) (guard : d8089 p = 1) : d1685 p ≤ (0 : Int) + d357 p := by
  cases selected : p 225 with
  | false =>
    have hg : d8084 p = 1 := by simpa only [d8089, d1685, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35444 p hg
    simpa only [d8089, d1685, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5847 p = 1 := by simpa only [d8089, d1685, d357, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38631 p hg
    simpa only [d8089, d1685, d357, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39630 (p : Pattern) (guard : d8094 p = 1) : d1686 p ≤ (0 : Int) + d358 p := by
  cases selected : p 224 with
  | false =>
    have hg : d8089 p = 1 := by simpa only [d8094, d1686, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39629 p hg
    simpa only [d8094, d1686, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d5854 p = 1 := by simpa only [d8094, d1686, d358, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38884 p hg
    simpa only [d8094, d1686, d358, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39631 (p : Pattern) (guard : d8100 p = 1) : d1687 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d1687, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39630 p hg
    simpa only [d8100, d1687, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d1687, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d1687, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39632 (p : Pattern) (guard : d8101 p = 1) : d1741 p ≤ (0 : Int) + d383 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8095 p = 1 := by simpa only [d8101, d1741, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39628 p hg
    simpa only [d8101, d1741, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8100 p = 1 := by simpa only [d8101, d1741, d383, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39631 p hg
    simpa only [d8101, d1741, d383, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39633 (p : Pattern) (guard : d8100 p = 1) : d32 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d32, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35590 p hg
    simpa only [d8100, d32, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d32, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d32, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39634 (p : Pattern) (guard : d8106 p = 1) : d1747 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1747, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39633 p hg
    simpa only [d8106, d1747, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1747, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38920 p hg
    simpa only [d8106, d1747, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39635 (p : Pattern) (guard : d8107 p = 1) : d1748 p ≤ (0 : Int) + d384 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1748, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39632 p hg
    simpa only [d8107, d1748, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1748, d384, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39634 p hg
    simpa only [d8107, d1748, d384, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39636 (p : Pattern) (guard : d8100 p = 1) : d19 p ≤ (0 : Int) + d367 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d19, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35596 p hg
    simpa only [d8100, d19, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d19, d367, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d19, d367, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39637 (p : Pattern) (guard : d8106 p = 1) : d1698 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1698, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39636 p hg
    simpa only [d8106, d1698, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1698, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38892 p hg
    simpa only [d8106, d1698, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39638 (p : Pattern) (guard : d8105 p = 1) : d25 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d25, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35600 p hg
    simpa only [d8105, d25, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d25, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d25, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39639 (p : Pattern) (guard : d8111 p = 1) : d1706 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1706, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39638 p hg
    simpa only [d8111, d1706, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1706, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15276 p hg
    simpa only [d8111, d1706, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39640 (p : Pattern) (guard : d8112 p = 1) : d1749 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1749, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39637 p hg
    simpa only [d8112, d1749, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1749, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39639 p hg
    simpa only [d8112, d1749, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39641 (p : Pattern) (guard : d8113 p = 1) : d1750 p ≤ (0 : Int) + d385 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1750, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39635 p hg
    simpa only [d8113, d1750, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1750, d385, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39640 p hg
    simpa only [d8113, d1750, d385, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39642 (p : Pattern) (guard : d8112 p = 1) : d1755 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1755, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39445 p hg
    simpa only [d8112, d1755, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1755, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39213 p hg
    simpa only [d8112, d1755, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39643 (p : Pattern) (guard : d8117 p = 1) : d1757 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1757, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39217 p hg
    simpa only [d8117, d1757, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1757, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1757, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39644 (p : Pattern) (guard : d8118 p = 1) : d1758 p ≤ (0 : Int) + d387 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1758, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39642 p hg
    simpa only [d8118, d1758, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1758, d387, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39643 p hg
    simpa only [d8118, d1758, d387, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39645 (p : Pattern) (guard : d8119 p = 1) : d1759 p ≤ (0 : Int) + d388 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1759, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39641 p hg
    simpa only [d8119, d1759, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1759, d388, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39644 p hg
    simpa only [d8119, d1759, d388, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39646 (p : Pattern) (guard : d8106 p = 1) : d1726 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1726, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39469 p hg
    simpa only [d8106, d1726, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1726, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38732 p hg
    simpa only [d8106, d1726, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39647 (p : Pattern) (guard : d8111 p = 1) : d1760 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1760, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39471 p hg
    simpa only [d8111, d1760, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1760, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d1760, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39648 (p : Pattern) (guard : d8112 p = 1) : d1761 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1761, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39646 p hg
    simpa only [d8112, d1761, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1761, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39647 p hg
    simpa only [d8112, d1761, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39649 (p : Pattern) (guard : d8118 p = 1) : d1763 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1763, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39648 p hg
    simpa only [d8118, d1763, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1763, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38934 p hg
    simpa only [d8118, d1763, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39650 (p : Pattern) (guard : d8124 p = 1) : d1766 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1766, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39649 p hg
    simpa only [d8124, d1766, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1766, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38939 p hg
    simpa only [d8124, d1766, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39651 (p : Pattern) (guard : d8125 p = 1) : d1767 p ≤ (0 : Int) + d392 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1767, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39645 p hg
    simpa only [d8125, d1767, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1767, d392, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39650 p hg
    simpa only [d8125, d1767, d392, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39652 (p : Pattern) (guard : d8126 p = 1) : d1768 p ≤ (0 : Int) + d393 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8120 p = 1 := by simpa only [d8126, d1768, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39626 p hg
    simpa only [d8126, d1768, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8125 p = 1 := by simpa only [d8126, d1768, d393, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39651 p hg
    simpa only [d8126, d1768, d393, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39653 (p : Pattern) (guard : d8132 p = 1) : d1826 p ≤ (0 : Int) + d401 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8126 p = 1 := by simpa only [d8132, d1826, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39652 p hg
    simpa only [d8132, d1826, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8131 p = 1 := by simpa only [d8132, d1826, d401, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39501 p hg
    simpa only [d8132, d1826, d401, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39654 (p : Pattern) (guard : d8107 p = 1) : d1784 p ≤ (0 : Int) + d346 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1784, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39516 p hg
    simpa only [d8107, d1784, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1784, d346, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39491 p hg
    simpa only [d8107, d1784, d346, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39655 (p : Pattern) (guard : d8106 p = 1) : d1790 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1790, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39469 p hg
    simpa only [d8106, d1790, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1790, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38956 p hg
    simpa only [d8106, d1790, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39656 (p : Pattern) (guard : d8112 p = 1) : d1800 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1800, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39655 p hg
    simpa only [d8112, d1800, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1800, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39496 p hg
    simpa only [d8112, d1800, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39657 (p : Pattern) (guard : d8113 p = 1) : d1801 p ≤ (0 : Int) + d402 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1801, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39654 p hg
    simpa only [d8113, d1801, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1801, d402, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39656 p hg
    simpa only [d8113, d1801, d402, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39658 (p : Pattern) (guard : d8118 p = 1) : d1807 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1807, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39482 p hg
    simpa only [d8118, d1807, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1807, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38961 p hg
    simpa only [d8118, d1807, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39659 (p : Pattern) (guard : d8119 p = 1) : d1808 p ≤ (0 : Int) + d404 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1808, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39657 p hg
    simpa only [d8119, d1808, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1808, d404, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39658 p hg
    simpa only [d8119, d1808, d404, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39660 (p : Pattern) (guard : d8112 p = 1) : d1811 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1811, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38863 p hg
    simpa only [d8112, d1811, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1811, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38964 p hg
    simpa only [d8112, d1811, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39661 (p : Pattern) (guard : d8118 p = 1) : d1812 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1812, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39660 p hg
    simpa only [d8118, d1812, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1812, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38751 p hg
    simpa only [d8118, d1812, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39662 (p : Pattern) (guard : d8124 p = 1) : d1813 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1813, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39661 p hg
    simpa only [d8124, d1813, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1813, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34736 p hg
    simpa only [d8124, d1813, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39663 (p : Pattern) (guard : d8125 p = 1) : d1814 p ≤ (0 : Int) + d406 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1814, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39659 p hg
    simpa only [d8125, d1814, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1814, d406, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39662 p hg
    simpa only [d8125, d1814, d406, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39664 (p : Pattern) (guard : d8106 p = 1) : d1783 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1783, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39541 p hg
    simpa only [d8106, d1783, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1783, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38951 p hg
    simpa only [d8106, d1783, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39665 (p : Pattern) (guard : d8111 p = 1) : d1809 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1809, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39543 p hg
    simpa only [d8111, d1809, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1809, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15281 p hg
    simpa only [d8111, d1809, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39666 (p : Pattern) (guard : d8112 p = 1) : d1815 p ≤ (0 : Int) + d369 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1815, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39664 p hg
    simpa only [d8112, d1815, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1815, d369, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39665 p hg
    simpa only [d8112, d1815, d369, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39667 (p : Pattern) (guard : d8111 p = 1) : d1799 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1799, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39546 p hg
    simpa only [d8111, d1799, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1799, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15333 p hg
    simpa only [d8111, d1799, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39668 (p : Pattern) (guard : d8117 p = 1) : d1816 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1816, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39667 p hg
    simpa only [d8117, d1816, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1816, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38972 p hg
    simpa only [d8117, d1816, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39669 (p : Pattern) (guard : d8118 p = 1) : d1817 p ≤ (0 : Int) + d372 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1817, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39666 p hg
    simpa only [d8118, d1817, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1817, d372, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39668 p hg
    simpa only [d8118, d1817, d372, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39670 (p : Pattern) (guard : d8117 p = 1) : d1818 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1818, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39496 p hg
    simpa only [d8117, d1818, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1818, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38975 p hg
    simpa only [d8117, d1818, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39671 (p : Pattern) (guard : d8123 p = 1) : d1819 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1819, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39670 p hg
    simpa only [d8123, d1819, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1819, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38977 p hg
    simpa only [d8123, d1819, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39672 (p : Pattern) (guard : d8124 p = 1) : d1820 p ≤ (0 : Int) + d376 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1820, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39669 p hg
    simpa only [d8124, d1820, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1820, d376, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39671 p hg
    simpa only [d8124, d1820, d376, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39673 (p : Pattern) (guard : d8130 p = 1) : d1824 p ≤ (0 : Int) + d407 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1824, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39672 p hg
    simpa only [d8130, d1824, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1824, d407, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38982 p hg
    simpa only [d8130, d1824, d407, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39674 (p : Pattern) (guard : d8131 p = 1) : d1825 p ≤ (0 : Int) + d408 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1825, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39663 p hg
    simpa only [d8131, d1825, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1825, d408, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39673 p hg
    simpa only [d8131, d1825, d408, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39675 (p : Pattern) (guard : d8106 p = 1) : d1805 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1805, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39033 p hg
    simpa only [d8106, d1805, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1805, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38558 p hg
    simpa only [d8106, d1805, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39676 (p : Pattern) (guard : d8112 p = 1) : d1827 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1827, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39675 p hg
    simpa only [d8112, d1827, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1827, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38750 p hg
    simpa only [d8112, d1827, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39677 (p : Pattern) (guard : d8118 p = 1) : d1828 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1828, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39676 p hg
    simpa only [d8118, d1828, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1828, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38751 p hg
    simpa only [d8118, d1828, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39678 (p : Pattern) (guard : d8124 p = 1) : d1830 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1830, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39677 p hg
    simpa only [d8124, d1830, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1830, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39505 p hg
    simpa only [d8124, d1830, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39679 (p : Pattern) (guard : d8130 p = 1) : d1832 p ≤ (0 : Int) + d410 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1832, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39678 p hg
    simpa only [d8130, d1832, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1832, d410, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39507 p hg
    simpa only [d8130, d1832, d410, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39680 (p : Pattern) (guard : d8123 p = 1) : d1829 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1829, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39643 p hg
    simpa only [d8123, d1829, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1829, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8123, d1829, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39681 (p : Pattern) (guard : d8129 p = 1) : d1831 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1831, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39680 p hg
    simpa only [d8129, d1831, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1831, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1831, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39682 (p : Pattern) (guard : d8135 p = 1) : d1833 p ≤ (0 : Int) + d411 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1833, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39681 p hg
    simpa only [d8135, d1833, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1833, d411, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8135, d1833, d411, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39683 (p : Pattern) (guard : d8136 p = 1) : d1834 p ≤ (0 : Int) + d412 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1834, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39679 p hg
    simpa only [d8136, d1834, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1834, d412, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39682 p hg
    simpa only [d8136, d1834, d412, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39684 (p : Pattern) (guard : d8137 p = 1) : d1835 p ≤ (0 : Int) + d413 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1835, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39674 p hg
    simpa only [d8137, d1835, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1835, d413, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39683 p hg
    simpa only [d8137, d1835, d413, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39685 (p : Pattern) (guard : d8138 p = 1) : d1836 p ≤ (0 : Int) + d414 p := by
  cases selected : p 116 with
  | false =>
    have hg : d8132 p = 1 := by simpa only [d8138, d1836, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39653 p hg
    simpa only [d8138, d1836, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8137 p = 1 := by simpa only [d8138, d1836, d414, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39684 p hg
    simpa only [d8138, d1836, d414, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39686 (p : Pattern) (guard : d5854 p = 1) : d1685 p ≤ (0 : Int) + d12 p := by
  cases selected : p 225 with
  | false =>
    have hg : d5847 p = 1 := by simpa only [d5854, d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34416 p hg
    simpa only [d5854, d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d5854, d1685, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17084 p hg
    simpa only [d5854, d1685, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39687 (p : Pattern) (guard : d8099 p = 1) : d1686 p ≤ (0 : Int) + d12 p := by
  cases selected : p 224 with
  | false =>
    have hg : d5854 p = 1 := by simpa only [d8099, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39686 p hg
    simpa only [d8099, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8099, d1686, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare17084 p hg
    simpa only [d8099, d1686, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39688 (p : Pattern) (guard : d8105 p = 1) : d1687 p ≤ (0 : Int) + d12 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39687 p hg
    simpa only [d8105, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d1687, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d1687, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39689 (p : Pattern) (guard : d8106 p = 1) : d1692 p ≤ (0 : Int) + d368 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1692, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39541 p hg
    simpa only [d8106, d1692, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1692, d368, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39688 p hg
    simpa only [d8106, d1692, d368, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39690 (p : Pattern) (guard : d8107 p = 1) : d1837 p ≤ (0 : Int) + d415 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8101 p = 1 := by simpa only [d8107, d1837, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39440 p hg
    simpa only [d8107, d1837, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8106 p = 1 := by simpa only [d8107, d1837, d415, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39689 p hg
    simpa only [d8107, d1837, d415, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39691 (p : Pattern) (guard : d8106 p = 1) : d1692 p ≤ (0 : Int) + d345 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1692, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39490 p hg
    simpa only [d8106, d1692, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1692, d345, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39688 p hg
    simpa only [d8106, d1692, d345, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39692 (p : Pattern) (guard : d8111 p = 1) : d1698 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1698, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39546 p hg
    simpa only [d8111, d1698, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1698, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15269 p hg
    simpa only [d8111, d1698, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39693 (p : Pattern) (guard : d8112 p = 1) : d1699 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1699, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39691 p hg
    simpa only [d8112, d1699, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1699, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39692 p hg
    simpa only [d8112, d1699, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39694 (p : Pattern) (guard : d8113 p = 1) : d1838 p ≤ (0 : Int) + d416 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8107 p = 1 := by simpa only [d8113, d1838, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39690 p hg
    simpa only [d8113, d1838, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8112 p = 1 := by simpa only [d8113, d1838, d416, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39693 p hg
    simpa only [d8113, d1838, d416, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39695 (p : Pattern) (guard : d8106 p = 1) : d1692 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1692, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39469 p hg
    simpa only [d8106, d1692, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1692, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39688 p hg
    simpa only [d8106, d1692, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39696 (p : Pattern) (guard : d8111 p = 1) : d1698 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1698, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39495 p hg
    simpa only [d8111, d1698, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1698, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15269 p hg
    simpa only [d8111, d1698, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39697 (p : Pattern) (guard : d8112 p = 1) : d1699 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1699, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39695 p hg
    simpa only [d8112, d1699, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1699, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39696 p hg
    simpa only [d8112, d1699, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39698 (p : Pattern) (guard : d8117 p = 1) : d1707 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38925 p hg
    simpa only [d8117, d1707, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1707, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8117, d1707, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39699 (p : Pattern) (guard : d8118 p = 1) : d1708 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1708, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39697 p hg
    simpa only [d8118, d1708, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1708, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39698 p hg
    simpa only [d8118, d1708, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39700 (p : Pattern) (guard : d8119 p = 1) : d1839 p ≤ (0 : Int) + d417 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8113 p = 1 := by simpa only [d8119, d1839, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39694 p hg
    simpa only [d8119, d1839, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8118 p = 1 := by simpa only [d8119, d1839, d417, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39699 p hg
    simpa only [d8119, d1839, d417, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39701 (p : Pattern) (guard : d8106 p = 1) : d1719 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1719, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35586 p hg
    simpa only [d8106, d1719, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1719, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38742 p hg
    simpa only [d8106, d1719, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39702 (p : Pattern) (guard : d8111 p = 1) : d1726 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34908 p hg
    simpa only [d8111, d1726, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1726, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15283 p hg
    simpa only [d8111, d1726, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39703 (p : Pattern) (guard : d8112 p = 1) : d1727 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1727, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39701 p hg
    simpa only [d8112, d1727, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1727, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39702 p hg
    simpa only [d8112, d1727, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39704 (p : Pattern) (guard : d8111 p = 1) : d1731 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34908 p hg
    simpa only [d8111, d1731, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1731, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15286 p hg
    simpa only [d8111, d1731, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39705 (p : Pattern) (guard : d8117 p = 1) : d1733 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39704 p hg
    simpa only [d8117, d1733, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1733, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39553 p hg
    simpa only [d8117, d1733, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39706 (p : Pattern) (guard : d8118 p = 1) : d1734 p ≤ (0 : Int) + d403 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1734, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39703 p hg
    simpa only [d8118, d1734, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1734, d403, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39705 p hg
    simpa only [d8118, d1734, d403, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39707 (p : Pattern) (guard : d8111 p = 1) : d1735 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34908 p hg
    simpa only [d8111, d1735, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1735, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8111, d1735, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39708 (p : Pattern) (guard : d8117 p = 1) : d1736 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39707 p hg
    simpa only [d8117, d1736, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1736, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39553 p hg
    simpa only [d8117, d1736, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39709 (p : Pattern) (guard : d0 p = 1) : d528 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39710 (p : Pattern) (guard : d8123 p = 1) : d1737 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39708 p hg
    simpa only [d8123, d1737, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1737, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39709 p hg
    simpa only [d8123, d1737, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39711 (p : Pattern) (guard : d8124 p = 1) : d1738 p ≤ (0 : Int) + d409 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1738, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39706 p hg
    simpa only [d8124, d1738, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1738, d409, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39710 p hg
    simpa only [d8124, d1738, d409, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39712 (p : Pattern) (guard : d8125 p = 1) : d1840 p ≤ (0 : Int) + d418 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8119 p = 1 := by simpa only [d8125, d1840, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39700 p hg
    simpa only [d8125, d1840, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8124 p = 1 := by simpa only [d8125, d1840, d418, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39711 p hg
    simpa only [d8125, d1840, d418, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39713 (p : Pattern) (guard : d8100 p = 1) : d15 p ≤ (0 : Int) + d351 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8094 p = 1 := by simpa only [d8100, d15, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35651 p hg
    simpa only [d8100, d15, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8099 p = 1 := by simpa only [d8100, d15, d351, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34488 p hg
    simpa only [d8100, d15, d351, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39714 (p : Pattern) (guard : d8106 p = 1) : d1692 p ≤ (0 : Int) + d352 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8100 p = 1 := by simpa only [d8106, d1692, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39713 p hg
    simpa only [d8106, d1692, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8105 p = 1 := by simpa only [d8106, d1692, d352, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39688 p hg
    simpa only [d8106, d1692, d352, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39715 (p : Pattern) (guard : d8105 p = 1) : d32 p ≤ (0 : Int) + d353 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d32, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35657 p hg
    simpa only [d8105, d32, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d32, d353, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d32, d353, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39716 (p : Pattern) (guard : d8111 p = 1) : d1747 p ≤ (0 : Int) + d354 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1747, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39715 p hg
    simpa only [d8111, d1747, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1747, d354, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15302 p hg
    simpa only [d8111, d1747, d354, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39717 (p : Pattern) (guard : d8112 p = 1) : d1841 p ≤ (0 : Int) + d355 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1841, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39714 p hg
    simpa only [d8112, d1841, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1841, d355, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39716 p hg
    simpa only [d8112, d1841, d355, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39718 (p : Pattern) (guard : d8105 p = 1) : d19 p ≤ (0 : Int) + d359 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d19, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35664 p hg
    simpa only [d8105, d19, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d19, d359, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d19, d359, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39719 (p : Pattern) (guard : d8111 p = 1) : d1698 p ≤ (0 : Int) + d360 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1698, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39718 p hg
    simpa only [d8111, d1698, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1698, d360, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15269 p hg
    simpa only [d8111, d1698, d360, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39720 (p : Pattern) (guard : d0 p = 1) : d1706 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39721 (p : Pattern) (guard : d8117 p = 1) : d1749 p ≤ (0 : Int) + d361 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1749, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39719 p hg
    simpa only [d8117, d1749, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1749, d361, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39720 p hg
    simpa only [d8117, d1749, d361, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39722 (p : Pattern) (guard : d8118 p = 1) : d1842 p ≤ (0 : Int) + d362 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1842, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39717 p hg
    simpa only [d8118, d1842, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1842, d362, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39721 p hg
    simpa only [d8118, d1842, d362, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39723 (p : Pattern) (guard : d8117 p = 1) : d1755 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1755, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39692 p hg
    simpa only [d8117, d1755, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1755, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38975 p hg
    simpa only [d8117, d1755, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39724 (p : Pattern) (guard : d8123 p = 1) : d1758 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1758, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39723 p hg
    simpa only [d8123, d1758, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1758, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare38977 p hg
    simpa only [d8123, d1758, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39725 (p : Pattern) (guard : d8124 p = 1) : d1843 p ≤ (0 : Int) + d395 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1843, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39722 p hg
    simpa only [d8124, d1843, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1843, d395, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39724 p hg
    simpa only [d8124, d1843, d395, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39726 (p : Pattern) (guard : d8111 p = 1) : d1726 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1726, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39589 p hg
    simpa only [d8111, d1726, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1726, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15283 p hg
    simpa only [d8111, d1726, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39727 (p : Pattern) (guard : d0 p = 1) : d1760 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39728 (p : Pattern) (guard : d8117 p = 1) : d1761 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1761, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39726 p hg
    simpa only [d8117, d1761, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1761, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39727 p hg
    simpa only [d8117, d1761, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39729 (p : Pattern) (guard : d0 p = 1) : d1762 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39730 (p : Pattern) (guard : d8123 p = 1) : d1763 p ≤ (0 : Int) + d375 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1763, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39728 p hg
    simpa only [d8123, d1763, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1763, d375, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39729 p hg
    simpa only [d8123, d1763, d375, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39731 (p : Pattern) (guard : d0 p = 1) : d1765 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39732 (p : Pattern) (guard : d8129 p = 1) : d1766 p ≤ (0 : Int) + d396 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1766, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39730 p hg
    simpa only [d8129, d1766, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1766, d396, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39731 p hg
    simpa only [d8129, d1766, d396, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39733 (p : Pattern) (guard : d8130 p = 1) : d1844 p ≤ (0 : Int) + d397 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1844, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39725 p hg
    simpa only [d8130, d1844, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1844, d397, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39732 p hg
    simpa only [d8130, d1844, d397, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39734 (p : Pattern) (guard : d8131 p = 1) : d1845 p ≤ (0 : Int) + d419 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8125 p = 1 := by simpa only [d8131, d1845, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39712 p hg
    simpa only [d8131, d1845, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8130 p = 1 := by simpa only [d8131, d1845, d419, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39733 p hg
    simpa only [d8131, d1845, d419, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39735 (p : Pattern) (guard : d8111 p = 1) : d1783 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1783, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39589 p hg
    simpa only [d8111, d1783, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1783, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15328 p hg
    simpa only [d8111, d1783, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39736 (p : Pattern) (guard : d8112 p = 1) : d1784 p ≤ (0 : Int) + d389 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1784, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39522 p hg
    simpa only [d8112, d1784, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1784, d389, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39735 p hg
    simpa only [d8112, d1784, d389, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39737 (p : Pattern) (guard : d8111 p = 1) : d1790 p ≤ (0 : Int) + d12 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare34908 p hg
    simpa only [d8111, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1790, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15331 p hg
    simpa only [d8111, d1790, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39738 (p : Pattern) (guard : d0 p = 1) : d1799 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39739 (p : Pattern) (guard : d8117 p = 1) : d1800 p ≤ (0 : Int) + d12 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39737 p hg
    simpa only [d8117, d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1800, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39738 p hg
    simpa only [d8117, d1800, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39740 (p : Pattern) (guard : d8118 p = 1) : d1801 p ≤ (0 : Int) + d390 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8112 p = 1 := by simpa only [d8118, d1801, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39736 p hg
    simpa only [d8118, d1801, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8117 p = 1 := by simpa only [d8118, d1801, d390, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39739 p hg
    simpa only [d8118, d1801, d390, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39741 (p : Pattern) (guard : d0 p = 1) : d1806 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39742 (p : Pattern) (guard : d8123 p = 1) : d1807 p ≤ (0 : Int) + d12 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39739 p hg
    simpa only [d8123, d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1807, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39741 p hg
    simpa only [d8123, d1807, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39743 (p : Pattern) (guard : d8124 p = 1) : d1808 p ≤ (0 : Int) + d391 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8118 p = 1 := by simpa only [d8124, d1808, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39740 p hg
    simpa only [d8124, d1808, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8123 p = 1 := by simpa only [d8124, d1808, d391, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39742 p hg
    simpa only [d8124, d1808, d391, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39744 (p : Pattern) (guard : d8129 p = 1) : d1813 p ≤ (0 : Int) + d12 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39570 p hg
    simpa only [d8129, d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1813, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8129, d1813, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39745 (p : Pattern) (guard : d8130 p = 1) : d1814 p ≤ (0 : Int) + d420 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8124 p = 1 := by simpa only [d8130, d1814, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39743 p hg
    simpa only [d8130, d1814, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8129 p = 1 := by simpa only [d8130, d1814, d420, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39744 p hg
    simpa only [d8130, d1814, d420, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39746 (p : Pattern) (guard : d8105 p = 1) : d15 p ≤ (0 : Int) + d336 p := by
  cases selected : p 204 with
  | false =>
    have hg : d8099 p = 1 := by simpa only [d8105, d15, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare35684 p hg
    simpa only [d8105, d15, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8105, d15, d336, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare1310 p hg
    simpa only [d8105, d15, d336, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39747 (p : Pattern) (guard : d8111 p = 1) : d1783 p ≤ (0 : Int) + d370 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1783, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39746 p hg
    simpa only [d8111, d1783, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1783, d370, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15328 p hg
    simpa only [d8111, d1783, d370, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39748 (p : Pattern) (guard : d8117 p = 1) : d1815 p ≤ (0 : Int) + d371 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1815, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39747 p hg
    simpa only [d8117, d1815, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1815, d371, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39578 p hg
    simpa only [d8117, d1815, d371, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39749 (p : Pattern) (guard : d0 p = 1) : d1816 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39750 (p : Pattern) (guard : d8123 p = 1) : d1817 p ≤ (0 : Int) + d394 p := by
  cases selected : p 162 with
  | false =>
    have hg : d8117 p = 1 := by simpa only [d8123, d1817, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39748 p hg
    simpa only [d8123, d1817, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8123, d1817, d394, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39749 p hg
    simpa only [d8123, d1817, d394, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39751 (p : Pattern) (guard : d0 p = 1) : d1819 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39752 (p : Pattern) (guard : d8129 p = 1) : d1820 p ≤ (0 : Int) + d405 p := by
  cases selected : p 161 with
  | false =>
    have hg : d8123 p = 1 := by simpa only [d8129, d1820, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39750 p hg
    simpa only [d8129, d1820, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8129, d1820, d405, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39751 p hg
    simpa only [d8129, d1820, d405, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39753 (p : Pattern) (guard : d0 p = 1) : d1823 p ≤ (0 : Int) + d12 p := by
  change (0 : Int) = 1 at guard
  omega
theorem compare39754 (p : Pattern) (guard : d8135 p = 1) : d1824 p ≤ (0 : Int) + d421 p := by
  cases selected : p 160 with
  | false =>
    have hg : d8129 p = 1 := by simpa only [d8135, d1824, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39752 p hg
    simpa only [d8135, d1824, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8135, d1824, d421, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39753 p hg
    simpa only [d8135, d1824, d421, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39755 (p : Pattern) (guard : d8136 p = 1) : d1825 p ≤ (0 : Int) + d422 p := by
  cases selected : p 141 with
  | false =>
    have hg : d8130 p = 1 := by simpa only [d8136, d1825, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39745 p hg
    simpa only [d8136, d1825, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8135 p = 1 := by simpa only [d8136, d1825, d422, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39754 p hg
    simpa only [d8136, d1825, d422, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39756 (p : Pattern) (guard : d8137 p = 1) : d1846 p ≤ (0 : Int) + d423 p := by
  cases selected : p 138 with
  | false =>
    have hg : d8131 p = 1 := by simpa only [d8137, d1846, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39734 p hg
    simpa only [d8137, d1846, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8136 p = 1 := by simpa only [d8137, d1846, d423, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39755 p hg
    simpa only [d8137, d1846, d423, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39757 (p : Pattern) (guard : d8112 p = 1) : d1784 p ≤ (0 : Int) + d386 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8106 p = 1 := by simpa only [d8112, d1784, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39520 p hg
    simpa only [d8112, d1784, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d8111 p = 1 := by simpa only [d8112, d1784, d386, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39747 p hg
    simpa only [d8112, d1784, d386, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39758 (p : Pattern) (guard : d8111 p = 1) : d1790 p ≤ (0 : Int) + d373 p := by
  cases selected : p 182 with
  | false =>
    have hg : d8105 p = 1 := by simpa only [d8111, d1790, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39589 p hg
    simpa only [d8111, d1790, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8111, d1790, d373, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare15331 p hg
    simpa only [d8111, d1790, d373, selected, Bool.false_eq_true, ↓reduceIte] using h
theorem compare39759 (p : Pattern) (guard : d8117 p = 1) : d1800 p ≤ (0 : Int) + d374 p := by
  cases selected : p 163 with
  | false =>
    have hg : d8111 p = 1 := by simpa only [d8117, d1800, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39758 p hg
    simpa only [d8117, d1800, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
  | true =>
    have hg : d0 p = 1 := by simpa only [d8117, d1800, d374, selected, Bool.false_eq_true, ↓reduceIte] using guard
    have h := compare39738 p hg
    simpa only [d8117, d1800, d374, selected, Bool.false_eq_true, ↓reduceIte] using h
end NetHack.Sokoban22Refined85
